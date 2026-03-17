{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | Multi-Agent server with HTTP REST + WebSocket push
-- Each Agent is a pure coalgebra (step : S -> I -> S, observe : S -> O)
-- Multiple agents can be registered at different paths
-- WebSocket clients on /ws receive broadcasts on any agent state change
--
-- Client ID tracking + peek/over protocol for Big Lens
module Agdelte.AgentServer
  ( AgentDef(..)
  , runAgentServer
  , mkAgentApp
  , splitPath
  , addCorsHeaders
  , ConnectionDef(..)
  , runAgentServerWithConns
  , mkAgentAppWithConns
  ) where

import Control.Concurrent.Async (race_)
import Control.Concurrent.STM
import Control.Concurrent.MVar
import Control.Exception (SomeAsyncException(..), SomeException, bracket_, finally, fromException, throwIO, try)
import System.IO (hPutStrLn, stderr, withBinaryFile, IOMode(..))
import qualified Data.IORef as IORef
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as Map
import System.Timeout (timeout)
import qualified Data.Set as Set
import Control.Monad (unless, when, forM_)
import Numeric (showHex)
import qualified Data.ByteString as BS
import Data.Word (Word8)

import qualified Network.Wai as Wai
import qualified Network.Wai.Handler.Warp as Warp

import qualified Agdelte.Http as Http
import qualified Agdelte.WebSocket as WS
import qualified Network.WebSockets as NWS

-- | Agent definition: name, path, observe, step.
-- IMPORTANT: agentObserve and agentStep must be thread-safe — they may be
-- called concurrently from multiple HTTP requests, WebSocket client routes,
-- and agent pipe connections. Use MVar or similar for internal synchronization
-- (see wireAgent in Server.agda for the reference implementation).
data AgentDef = AgentDef
  { agentName    :: Text
  , agentPath    :: Text                      -- e.g. "/counter"
  , agentObserve :: IO Text                   -- get current observable output
  , agentStep    :: Text -> IO Text           -- step with input, return output
  }

-- | Connection routing definition (from Diagram)
data ConnectionDef
  = BroadcastDef Text        -- ^ Agent output → all WS clients
  | AgentPipeDef Text Text   -- ^ Source agent output → target agent input
  | ClientRouteDef Text      -- ^ WS client messages → agent input

-- | Extract all agent names referenced by a connection definition
connDefNames :: ConnectionDef -> [Text]
connDefNames (BroadcastDef n)    = [n]
connDefNames (AgentPipeDef s t)  = [s, t]
connDefNames (ClientRouteDef n)  = [n]

-- | Shared broadcast channel for WebSocket clients
type BroadcastChan = TChan Text

-- | Connected client with unique ID and direct send capability
data WsClient = WsClient
  { clientId   :: Text
  , clientConn :: WS.WsConn
  , clientPeekNonce   :: IORef.IORef Int  -- nonce counter for peek requests
  , clientPeekSlots   :: TVar (Map.Map Int (MVar Text))  -- nonce → response slot
  }

-- | Client registry: clientId -> WsClient
type ClientRegistry = TVar (Map.Map Text WsClient)

-- | Build a WAI Application (no connection routing).
-- Auto-generates BroadcastDef for each agent so WS clients receive
-- state updates on every step (matching pre-deduplication behavior).
mkAgentApp :: Maybe Text -> [AgentDef] -> IO Wai.Application
mkAgentApp corsOrigin agents =
  mkAgentAppWithConns corsOrigin agents
    [BroadcastDef (agentName a) | a <- agents]

-- | Run multi-agent server (no connection routing)
runAgentServer :: Int -> Maybe Text -> [AgentDef] -> IO ()
runAgentServer port corsOrigin agents =
  runAgentServerWithConns port corsOrigin agents
    [BroadcastDef (agentName a) | a <- agents]

addCorsHeaders :: Maybe Text -> Http.Response -> Http.Response
addCorsHeaders Nothing resp = resp
addCorsHeaders (Just origin) resp = resp { Http.resHeaders = Http.resHeaders resp ++
  [ ("Access-Control-Allow-Origin", origin)
  , ("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
  , ("Access-Control-Allow-Headers", "*")
  , ("Access-Control-Max-Age", "3600")
  , ("Vary", "Origin")
  ] }

-- | Plain-text response (non-JSON errors, ack messages)
textResponse :: Int -> Text -> Http.Response
textResponse status body = Http.Response status body [("Content-Type", "text/plain; charset=utf-8")]

-- | 405 Method Not Allowed with required Allow header (RFC 7231 §6.5.5)
methodNotAllowed :: Text -> Text -> Http.Response
methodNotAllowed allow msg = Http.Response 405 msg
  [ ("Content-Type", "text/plain; charset=utf-8")
  , ("Allow", allow)
  ]

-- | Handle /client/{clientId}/{action} requests
-- GET /client/{clientId}/peek -> peek client model via WS
-- POST /client/{clientId}/over -> send msg to client via WS
handleClientRequest :: ClientRegistry -> Text -> Text -> Text -> IO Http.Response
handleClientRequest registry method rest body = do
  let (clientId', action) = case T.breakOn "/" rest of
        (cid, rest') | not (T.null rest') -> (cid, T.drop 1 rest')
        (cid, _) -> (cid, "peek")
  clients <- atomically $ readTVar registry
  case Map.lookup clientId' clients of
    Nothing -> return $ textResponse 404 "Client not found"
    Just client -> case action of
      "peek"
        | method /= "GET" && method /= "HEAD" -> return $ methodNotAllowed "GET, HEAD" "Use GET for /peek"
        | otherwise -> do
        -- Per-request MVar peek protocol: each peek gets a fresh MVar keyed by
        -- nonce, so stale/concurrent responses cannot interfere.
        -- Protocol: peek:clientId:nonce → peek-response:nonce:value
        nonce <- IORef.atomicModifyIORef' (clientPeekNonce client) (\n -> (n + 1, n + 1))
        let nonceText = T.pack (show nonce)
        slot <- newEmptyMVar
        atomically $ modifyTVar' (clientPeekSlots client)
          (Map.insert nonce slot)
        -- Guarantee slot cleanup even on async exceptions
        (do result <- try $ WS.wsSend (clientConn client) ("peek:" <> clientId' <> ":" <> nonceText)
            case result of
              Left (e :: SomeException) | Just (SomeAsyncException _) <- fromException e -> throwIO e
              Left _ ->
                return $ textResponse 502 "Client disconnected"
              Right () -> do
                mResponse <- timeout 5000000 $ takeMVar slot
                case mResponse of
                  Just value ->
                    return $ Http.Response 200 value []
                  Nothing -> return $ textResponse 504 "Client peek timeout"
         ) `finally` atomically (modifyTVar' (clientPeekSlots client) (Map.delete nonce))
      "over"
        | method /= "POST" -> return $ methodNotAllowed "POST" "Use POST for /over"
        | otherwise -> do
        result <- try $ WS.wsSend (clientConn client) ("over:" <> body)
        case result of
          Left (e :: SomeException) | Just (SomeAsyncException _) <- fromException e -> throwIO e
          Left _ ->
            return $ textResponse 502 "Client disconnected"
          Right () ->
            return $ textResponse 200 "ok"
      _ -> return $ textResponse 404 "Unknown client action (use /peek or /over)"

-- | Split "/counter/step" into ("/counter", "step").
-- Only the first two path segments are used; extra segments (e.g.
-- "/counter/step/extra") are silently ignored. The protocol only
-- supports /{agent}/{action} where action is "state" or "step".
splitPath :: Text -> (Text, Text)
splitPath path =
  let parts = filter (not . T.null) (T.splitOn "/" path)
  in case parts of
    []     -> ("/", "state")       -- default to state (consistent with single-segment)
    [p]    -> ("/" <> p, "state")  -- default to state
    (p:a:_) -> ("/" <> p, a)

-- | Maximum number of buffered broadcast messages per client.
-- If a slow client falls behind by this many messages, the oldest are dropped.
maxBroadcastBacklog :: Int
maxBroadcastBacklog = 256

-- | Forward broadcasts to this client via a bounded TQueue.
-- A feeder thread copies from TChan to TQueue, dropping oldest when full.
-- This prevents unbounded memory growth for slow WebSocket clients.
broadcastLoop :: WS.WsConn -> TChan Text -> IO ()
broadcastLoop conn ch = do
  q <- newTQueueIO
  qLen <- newTVarIO (0 :: Int)
  race_ (feeder ch q qLen) (sender conn q qLen)
  where
    feeder chan queue lenVar = do
      atomically $ do
        msg <- readTChan chan
        len <- readTVar lenVar
        when (len >= maxBroadcastBacklog) $ do
          _ <- readTQueue queue  -- drop oldest
          writeTVar lenVar (len - 1)
        writeTQueue queue msg
        modifyTVar' lenVar (+ 1)
      feeder chan queue lenVar
    sender connection queue lenVar = do
      msg <- atomically $ do
        m <- readTQueue queue
        modifyTVar' lenVar (subtract 1)
        return m
      result <- try $ WS.wsSend connection msg
      case result of
        Left (e :: SomeException) | Just (SomeAsyncException _) <- fromException e -> throwIO e
        Left _ -> return ()  -- connection gone, exit cleanly
        Right () -> sender connection queue lenVar

------------------------------------------------------------------------
-- Connection-aware server (Diagram routing)
------------------------------------------------------------------------

-- | Precomputed connection routing tables (built once at server start)
data ConnRouting = ConnRouting
  { crBroadcasts   :: Set.Set Text                     -- ^ agents that broadcast
  , crPipes        :: Map.Map Text [Text]              -- ^ source → [target]
  , crNameMap      :: Map.Map Text AgentDef             -- ^ agent name → def
  , crClientRoutes :: Set.Set Text                        -- ^ client route targets
  }

mkConnRouting :: Map.Map Text AgentDef -> [ConnectionDef] -> ConnRouting
mkConnRouting nameMap conns = ConnRouting
  { crBroadcasts   = Set.fromList [n | BroadcastDef n <- conns]
  , crPipes        = Map.map (Set.toList . Set.fromList) (Map.fromListWith (++) [(s, [t]) | AgentPipeDef s t <- conns])
  , crNameMap      = nameMap
  , crClientRoutes = Set.fromList [n | ClientRouteDef n <- conns]
  }

-- | Maximum pipe chain depth (prevents stack overflow on long non-cyclic chains).
maxPipeDepth :: Int
maxPipeDepth = 64

-- | Apply connection routing after an agent step.
-- Handles broadcast to WS, agent pipes (with cycle detection and depth limit).
applyConnections :: ConnRouting -> BroadcastChan
                 -> Set.Set Text -> Text -> Text -> IO ()
applyConnections routing broadcast visited source output =
  applyConnectionsDepth routing broadcast visited source output 0

applyConnectionsDepth :: ConnRouting -> BroadcastChan
                      -> Set.Set Text -> Text -> Text -> Int -> IO ()
applyConnectionsDepth routing broadcast visited source output depth
  | depth >= maxPipeDepth = do
      hPutStrLn stderr $ "AgentServer: pipe chain depth limit (" ++ show maxPipeDepth
        ++ ") reached at agent " ++ T.unpack source ++ ", stopping propagation"
  | Set.member source visited = do  -- cycle detected, stop
      hPutStrLn stderr $ "AgentServer: cycle detected in pipe chain at agent "
        ++ T.unpack source ++ ", stopping propagation"
  | otherwise = do
      let visited' = Set.insert source visited
      -- Broadcast to WS clients if declared
      when (Set.member source (crBroadcasts routing)) $
        atomically $ writeTChan broadcast (source <> ":" <> output)
      -- Pipe to target agents (each pipe is independently exception-safe)
      let targets = Map.findWithDefault [] source (crPipes routing)
      forM_ targets $ \target ->
        case Map.lookup target (crNameMap routing) of
          Nothing -> hPutStrLn stderr $
            "AgentServer: pipe target not found: " ++ T.unpack target
          Just targetAgent -> do
            result <- try $ agentStep targetAgent output
            case result of
              Left (e :: SomeException)
                | Just (SomeAsyncException _) <- fromException e -> throwIO e
                | otherwise ->
                hPutStrLn stderr $ "AgentServer: pipe step failed for "
                  ++ T.unpack target ++ ": " ++ show e
              Right targetOutput ->
                applyConnectionsDepth routing broadcast visited' target targetOutput (depth + 1)

-- | Build a WAI Application with connection routing.
-- Allocates broadcast channel, client registry, and counter internally.
-- Useful for testing (Warp.testWithApplication) without starting a server.
mkAgentAppWithConns :: Maybe Text -> [AgentDef] -> [ConnectionDef] -> IO Wai.Application
mkAgentAppWithConns corsOrigin agents conns = do
  broadcast <- newBroadcastTChanIO
  registry  <- newTVarIO Map.empty
  clientCounter <- IORef.newIORef (0 :: Int)
  sessionId <- generateSessionId
  let routeMap = Map.fromList [(agentPath a, a) | a <- agents]
      nameMap  = Map.fromList [(agentName a, a) | a <- agents]
      routing  = mkConnRouting nameMap conns
  when (Map.size routeMap /= length agents) $
    hPutStrLn stderr "WARNING: duplicate agent paths detected — some agents will be shadowed"
  when (Map.size nameMap /= length agents) $
    hPutStrLn stderr "WARNING: duplicate agent names detected — some agents will be shadowed"
  when (Map.member "/client" routeMap) $
    hPutStrLn stderr "WARNING: agent at path \"/client\" shadows /client/{id}/peek and /client/{id}/over endpoints"
  -- Validate that all connection defs reference registered agents
  let connNames = concatMap connDefNames conns
      unknowns = filter (\n -> not (Map.member n nameMap)) connNames
  forM_ unknowns $ \n ->
    hPutStrLn stderr $ "WARNING: connection references unknown agent: " ++ T.unpack n
  -- Warn about self-referencing pipes
  let selfPipes = [(s, t) | AgentPipeDef s t <- conns, s == t]
  forM_ selfPipes $ \(s, _) ->
    hPutStrLn stderr $ "WARNING: self-referencing pipe on agent " ++ T.unpack s
      ++ " — will always trigger cycle detection"
  -- Warn about duplicate pipe definitions (O(n log n) via Map)
  let pipePairs = [(s, t) | AgentPipeDef s t <- conns]
      pipeCounts = Map.fromListWith ((+) :: Int -> Int -> Int) [(p, 1 :: Int) | p <- pipePairs]
      hasDups = any (> 1) (Map.elems pipeCounts)
  when hasDups $
    hPutStrLn stderr $ "WARNING: duplicate pipe definitions detected (duplicates are deduplicated)"
  return $ Http.mkApp
    (connHttpHandler corsOrigin routeMap routing registry broadcast)
    (Just ("/ws", connWsHandler broadcast registry clientCounter sessionId routing))

-- | Run multi-agent server with connection routing
runAgentServerWithConns :: Int -> Maybe Text -> [AgentDef] -> [ConnectionDef] -> IO ()
runAgentServerWithConns port corsOrigin agents conns = do
  putStrLn $ "Agdelte Agent Server on port " ++ show port
  putStrLn $ "  Agents: " ++ show [T.unpack (agentName a) ++ " at " ++ T.unpack (agentPath a) | a <- agents]
  putStrLn $ "  Connections: " ++ show (length conns)
  putStrLn "  WebSocket: /ws (connection routing active)"
  app <- mkAgentAppWithConns corsOrigin agents conns
  Warp.runSettings settings app
  where
    settings = Warp.setPort port $ Warp.setHost "*" $ Warp.defaultSettings

connHttpHandler :: Maybe Text -> Map.Map Text AgentDef -> ConnRouting
               -> ClientRegistry -> BroadcastChan
               -> Http.Request -> IO Http.Response
connHttpHandler corsOrigin routes routing registry broadcast req
  | Http.reqMethod req == "OPTIONS" = return $ addCorsHeaders corsOrigin (Http.Response 204 T.empty [])
  | otherwise = do
      let method = Http.reqMethod req
          path = Http.reqPath req
          body = Http.reqBody req
      resp <- connRouteRequest routes routing registry broadcast method path body
      return $ addCorsHeaders corsOrigin resp

connRouteRequest :: Map.Map Text AgentDef -> ConnRouting
                -> ClientRegistry -> BroadcastChan
                -> Text -> Text -> Text -> IO Http.Response
connRouteRequest routes routing registry broadcast method path body
  -- Check /client/ prefix first to prevent agent paths from shadowing it
  | Just rest <- T.stripPrefix "/client/" path =
      handleClientRequest registry method rest body
  | otherwise = do
  let (agentPath', action) = splitPath path
  case Map.lookup agentPath' routes of
    Just agent -> case action of
          "state"
            | method /= "GET" && method /= "HEAD" -> return $ methodNotAllowed "GET, HEAD" "Use GET for /state"
            | otherwise -> do
                result <- try $ agentObserve agent
                case result of
                  Left (e :: SomeException)
                    | Just (SomeAsyncException _) <- fromException e -> throwIO e
                    | otherwise -> do
                    hPutStrLn stderr $ "AgentServer: observe failed for "
                      ++ T.unpack (agentName agent) ++ ": " ++ show e
                    return $ textResponse 500 "Internal server error"
                  Right output ->
                    return $ Http.Response 200 output []
          "step"
            | method /= "POST" -> return $ methodNotAllowed "POST" "Use POST for /step"
            | otherwise -> do
                result <- try $ agentStep agent body
                case result of
                  Left (e :: SomeException)
                    | Just (SomeAsyncException _) <- fromException e -> throwIO e
                    | otherwise -> do
                    hPutStrLn stderr $ "AgentServer: step failed for "
                      ++ T.unpack (agentName agent) ++ ": " ++ show e
                    return $ textResponse 500 "Internal server error"
                  Right output -> do
                    -- Apply connection routing (broadcast + pipes).
                    -- Catch sync exceptions so a routing failure doesn't turn
                    -- the already-committed step into an HTTP 500.
                    connResult <- try $ applyConnections routing broadcast Set.empty (agentName agent) output
                    case connResult of
                      Left (e2 :: SomeException)
                        | Just (SomeAsyncException _) <- fromException e2 -> throwIO e2
                        | otherwise ->
                        hPutStrLn stderr $ "AgentServer: post-step connection routing failed for "
                          ++ T.unpack (agentName agent) ++ ": " ++ show e2
                      Right () -> return ()
                    return $ Http.Response 200 output []
          _ -> return $ textResponse 404 "Unknown action (use /state or /step)"
    Nothing -> return $ textResponse 404 "Agent not found"

connWsHandler :: BroadcastChan -> ClientRegistry -> IORef.IORef Int -> Text
             -> ConnRouting
             -> NWS.PendingConnection -> IO ()
connWsHandler broadcast registry counter sessionId routing pending = do
  result <- try $ NWS.acceptRequest pending
  case result of
    Left (e :: SomeException) | Just (SomeAsyncException _) <- fromException e -> throwIO e
    Left e -> hPutStrLn stderr $ "AgentServer: WebSocket accept failed: " ++ show e
    Right conn -> do
      cid <- IORef.atomicModifyIORef' counter (\n -> (n + 1, n))
      let clientId' = sessionId <> "-" <> T.pack (show cid)
      connWsHandlerBody broadcast registry clientId' (WS.mkWsConn conn) routing

connWsHandlerBody :: BroadcastChan -> ClientRegistry -> Text -> WS.WsConn
                 -> ConnRouting -> IO ()
connWsHandlerBody broadcast registry clientId' conn routing = do
  nonceRef <- IORef.newIORef (0 :: Int)
  slotsVar <- newTVarIO Map.empty
  let client = WsClient clientId' conn nonceRef slotsVar
  ch <- atomically $ dupTChan broadcast
  bracket_
    (atomically $ modifyTVar' registry (Map.insert clientId' client))
    (do atomically $ modifyTVar' registry (Map.delete clientId')
        -- Don't fill pending peek slots — let timeout handle in-flight requests.
        -- Filling with "" would cause 200 with empty body instead of 504 timeout.
        WS.wsClose conn)
    (do result <- try $ WS.wsSend conn ("connected:" <> clientId')
        case result of
          Left (e :: SomeException) | Just (SomeAsyncException _) <- fromException e -> throwIO e
          Left _ -> return ()  -- client disconnected before welcome
          Right () ->
            NWS.withPingThread (WS.unwrapConn conn) 30 (return ()) $
              race_ (broadcastLoop conn ch) (connClientLoop client routing broadcast))

-- | Generate a cryptographically random session ID (16 hex chars = 8 random bytes).
-- Uses /dev/urandom for unpredictable client IDs, preventing other clients from
-- guessing IDs to hit /client/{id}/peek or /client/{id}/over.
generateSessionId :: IO Text
generateSessionId = do
  bytes <- withBinaryFile "/dev/urandom" ReadMode (\h -> BS.hGet h 8)
  return $ T.pack $ concatMap toHex (BS.unpack bytes)
  where
    toHex :: Word8 -> String
    toHex b = let s = showHex b "" in if length s < 2 then '0':s else s

-- | Connection-aware client loop: routes WS messages via ClientRouteDef
connClientLoop :: WsClient -> ConnRouting -> BroadcastChan -> IO ()
connClientLoop client routing broadcast = do
  wsMsg <- WS.wsReceive (clientConn client)
  case wsMsg of
    WS.WsText msg -> do
      case T.stripPrefix "peek-response:" msg of
        Just nonceAndValue ->
          -- Response format: "nonce:value" — route to the correct slot
          case T.breakOn ":" nonceAndValue of
            (nonceText, rest) | not (T.null rest) ->
              case reads (T.unpack nonceText) of
                [(n, "")] -> do
                  mSlot <- atomically $ do
                    slots <- readTVar (clientPeekSlots client)
                    return (Map.lookup n slots)
                  case mSlot of
                    Just slot -> do
                      ok <- tryPutMVar slot (T.drop 1 rest)
                      unless ok $
                        hPutStrLn stderr $ "AgentServer: peek slot already filled for nonce "
                          ++ show n ++ " on " ++ T.unpack (clientId client)
                    Nothing ->
                      hPutStrLn stderr $ "AgentServer: peek response for unknown nonce "
                        ++ show n ++ " on " ++ T.unpack (clientId client)
                _ -> hPutStrLn stderr $ "AgentServer: malformed peek-response nonce from "
                       ++ T.unpack (clientId client)
            _ -> hPutStrLn stderr $ "AgentServer: malformed peek-response from "
                   ++ T.unpack (clientId client)
        Nothing ->
          -- Route client message to agents via ClientRouteDef.
          -- Message format: "agentName:payload" routes to specific agent.
          -- Only split on colon if the prefix matches a known route target;
          -- otherwise treat the entire message as payload. This prevents
          -- colon-containing payloads from being misinterpreted.
          -- With multiple routes, untagged messages are dropped with a warning.
          let routeTargets = crClientRoutes routing
              (targetName, payload) = case T.breakOn ":" msg of
                (name, rest)
                  | not (T.null rest), Set.member name routeTargets ->
                    (Just name, T.drop 1 rest)
                _ -> (Nothing, msg)
          in case targetName of
            Nothing | Set.size routeTargets > 1 ->
              hPutStrLn stderr $ "AgentServer: untagged WS message in multi-route setup, dropping: "
                ++ T.unpack (T.take 80 msg)
            _ -> forM_ (Set.toList routeTargets) $ \target ->
              case targetName of
                Just tn | tn /= target -> return ()  -- skip non-matching agents
                _ ->
                  case Map.lookup target (crNameMap routing) of
                    Nothing -> return ()
                    Just agent -> do
                      result <- try $ agentStep agent payload
                      case result of
                        Left (e :: SomeException)
                          | Just (SomeAsyncException _) <- fromException e -> throwIO e
                          | otherwise ->
                          hPutStrLn stderr $ "AgentServer: client route step failed for "
                            ++ T.unpack target ++ ": " ++ show e
                        Right output -> do
                          -- Catch sync exceptions so a routing failure doesn't
                          -- disconnect the WS client (mirrors HTTP-side fix).
                          connResult <- try $ applyConnections routing broadcast Set.empty target output
                          case connResult of
                            Left (e2 :: SomeException)
                              | Just (SomeAsyncException _) <- fromException e2 -> throwIO e2
                              | otherwise ->
                              hPutStrLn stderr $ "AgentServer: post-step WS routing failed for "
                                ++ T.unpack target ++ ": " ++ show e2
                            Right () -> return ()
      connClientLoop client routing broadcast
    WS.WsClose -> return ()
