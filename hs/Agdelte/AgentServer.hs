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
import Control.Exception (IOException, SomeException, bracket_, try)
import System.IO (hPutStrLn, stderr)
import qualified Data.IORef as IORef
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as Map
import System.Timeout (timeout)
import qualified Data.Set as Set
import Control.Monad (unless, when, forM_)
import Data.List (nub)
import Data.Unique (newUnique, hashUnique)
import Data.Word (Word)
import Numeric (showHex)

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
  ] }

-- | Handle /client/{clientId}/{action} requests
-- GET /client/{clientId}/peek -> peek client model via WS
-- POST /client/{clientId}/over -> send msg to client via WS
handleClientRequest :: ClientRegistry -> Text -> Text -> IO Http.Response
handleClientRequest registry rest body = do
  let (clientId', action) = case T.breakOn "/" rest of
        (cid, rest') | not (T.null rest') -> (cid, T.drop 1 rest')
        (cid, _) -> (cid, "peek")
  clients <- atomically $ readTVar registry
  case Map.lookup clientId' clients of
    Nothing -> return $ Http.Response 404 ("Client not found: " <> clientId') []
    Just client -> case action of
      "peek" -> do
        -- Per-request MVar peek protocol: each peek gets a fresh MVar keyed by
        -- nonce, so stale/concurrent responses cannot interfere.
        -- Protocol: peek:clientId:nonce → peek-response:nonce:value
        nonce <- IORef.atomicModifyIORef' (clientPeekNonce client) (\n -> (n + 1, n + 1))
        let nonceText = T.pack (show nonce)
        slot <- newEmptyMVar
        atomically $ modifyTVar' (clientPeekSlots client)
          (Map.insert nonce slot)
        result <- try $ WS.wsSend (clientConn client) ("peek:" <> clientId' <> ":" <> nonceText)
        case result of
          Left (_ :: SomeException) -> do
            atomically $ modifyTVar' (clientPeekSlots client) (Map.delete nonce)
            return $ Http.Response 502 "Client disconnected" []
          Right () -> do
            mResponse <- timeout 5000000 $ takeMVar slot
            atomically $ modifyTVar' (clientPeekSlots client) (Map.delete nonce)
            case mResponse of
              Just value ->
                return $ Http.Response 200 value []
              Nothing -> return $ Http.Response 504 "Client peek timeout" []
      "over" -> do
        result <- try $ WS.wsSend (clientConn client) ("over:" <> body)
        case result of
          Left (_ :: SomeException) ->
            return $ Http.Response 502 "Client disconnected" []
          Right () ->
            return $ Http.Response 200 "ok" []
      _ -> return $ Http.Response 404 "Unknown client action (use /peek or /over)" []

-- | Split "/counter/step" into ("/counter", "step").
-- Only the first two path segments are used; extra segments (e.g.
-- "/counter/step/extra") are silently ignored. The protocol only
-- supports /{agent}/{action} where action is "state" or "step".
splitPath :: Text -> (Text, Text)
splitPath path =
  let parts = filter (not . T.null) (T.splitOn "/" path)
  in case parts of
    []     -> ("/", "")
    [p]    -> ("/" <> p, "state")  -- default to state
    (p:a:_) -> ("/" <> p, a)

-- | Forward broadcasts to this client.
-- Catches send exceptions silently — if the connection is gone, the loop
-- exits and race_ cancels the client loop.
broadcastLoop :: WS.WsConn -> TChan Text -> IO ()
broadcastLoop conn ch = do
  msg <- atomically $ readTChan ch
  result <- try $ WS.wsSend conn msg
  case result of
    Left (_ :: SomeException) -> return ()  -- connection gone, exit cleanly
    Right () -> broadcastLoop conn ch

------------------------------------------------------------------------
-- Connection-aware server (Diagram routing)
------------------------------------------------------------------------

-- | Precomputed connection routing tables (built once at server start)
data ConnRouting = ConnRouting
  { crBroadcasts   :: Set.Set Text                     -- ^ agents that broadcast
  , crPipes        :: Map.Map Text [Text]              -- ^ source → [target]
  , crNameMap      :: Map.Map Text AgentDef             -- ^ agent name → def
  , crClientRoutes :: [Text]                            -- ^ client route targets
  }

mkConnRouting :: Map.Map Text AgentDef -> [ConnectionDef] -> ConnRouting
mkConnRouting nameMap conns = ConnRouting
  { crBroadcasts   = Set.fromList [n | BroadcastDef n <- conns]
  , crPipes        = Map.map nub (Map.fromListWith (++) [(s, [t]) | AgentPipeDef s t <- conns])
  , crNameMap      = nameMap
  , crClientRoutes = nub [n | ClientRouteDef n <- conns]
  }

-- | Apply connection routing after an agent step.
-- Handles broadcast to WS, agent pipes (with cycle detection).
applyConnections :: ConnRouting -> BroadcastChan
                 -> Set.Set Text -> Text -> Text -> IO ()
applyConnections routing broadcast visited source output
  | Set.member source visited = return ()  -- cycle detected, stop
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
              Left (e :: IOException) ->
                hPutStrLn stderr $ "AgentServer: pipe step failed for "
                  ++ T.unpack target ++ ": " ++ show e
              Right targetOutput ->
                applyConnections routing broadcast visited' target targetOutput

-- | Build a WAI Application with connection routing.
-- Allocates broadcast channel, client registry, and counter internally.
-- Useful for testing (Warp.testWithApplication) without starting a server.
mkAgentAppWithConns :: Maybe Text -> [AgentDef] -> [ConnectionDef] -> IO Wai.Application
mkAgentAppWithConns corsOrigin agents conns = do
  broadcast <- newBroadcastTChanIO
  registry  <- newTVarIO Map.empty
  clientCounter <- IORef.newIORef (0 :: Int)
  sessionId <- T.pack . flip showHex "" . (fromIntegral :: Int -> Word) . hashUnique <$> newUnique
  let routeMap = Map.fromList [(agentPath a, a) | a <- agents]
      nameMap  = Map.fromList [(agentName a, a) | a <- agents]
      routing  = mkConnRouting nameMap conns
  when (Map.size routeMap /= length agents) $
    hPutStrLn stderr "WARNING: duplicate agent paths detected — some agents will be shadowed"
  when (Map.size nameMap /= length agents) $
    hPutStrLn stderr "WARNING: duplicate agent names detected — some agents will be shadowed"
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
  | Http.reqMethod req == "OPTIONS" = return $ addCorsHeaders corsOrigin (Http.Response 200 T.empty [])
  | otherwise = do
      let method = Http.reqMethod req
          path = Http.reqPath req
          body = Http.reqBody req
      resp <- connRouteRequest routes routing registry broadcast method path body
      return $ addCorsHeaders corsOrigin resp

connRouteRequest :: Map.Map Text AgentDef -> ConnRouting
                -> ClientRegistry -> BroadcastChan
                -> Text -> Text -> Text -> IO Http.Response
connRouteRequest routes routing registry broadcast method path body = do
  let (agentPath', action) = splitPath path
  case Map.lookup agentPath' routes of
    Just agent -> case action of
          "state"
            | method == "POST" -> return $ Http.Response 405 "Use GET for /state" []
            | otherwise -> do
                result <- try $ agentObserve agent
                case result of
                  Left (e :: IOException) -> do
                    hPutStrLn stderr $ "AgentServer: observe failed for "
                      ++ T.unpack (agentName agent) ++ ": " ++ show e
                    return $ Http.Response 500 "Internal server error" []
                  Right output ->
                    return $ Http.Response 200 output []
          "step"
            | method == "GET" -> return $ Http.Response 405 "Use POST for /step" []
            | otherwise -> do
                result <- try $ agentStep agent body
                case result of
                  Left (e :: IOException) -> do
                    hPutStrLn stderr $ "AgentServer: step failed for "
                      ++ T.unpack (agentName agent) ++ ": " ++ show e
                    return $ Http.Response 500 "Internal server error" []
                  Right output -> do
                    -- Apply connection routing (broadcast + pipes)
                    applyConnections routing broadcast Set.empty (agentName agent) output
                    return $ Http.Response 200 output []
          _ -> return $ Http.Response 404 "Unknown action (use /state or /step)" []
    Nothing -> case T.stripPrefix "/client/" path of
      Just rest -> handleClientRequest registry rest body
      Nothing -> return $ Http.Response 404 "Agent not found" []

connWsHandler :: BroadcastChan -> ClientRegistry -> IORef.IORef Int -> Text
             -> ConnRouting
             -> NWS.PendingConnection -> IO ()
connWsHandler broadcast registry counter sessionId routing pending = do
  result <- try $ NWS.acceptRequest pending
  case result of
    Left (_ :: SomeException) -> return ()
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
        WS.wsClose conn)
    (do result <- try $ WS.wsSend conn ("connected:" <> clientId')
        case result of
          Left (_ :: SomeException) -> return ()  -- client disconnected before welcome
          Right () ->
            race_ (broadcastLoop conn ch) (connClientLoop client routing broadcast))

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
          -- Untagged messages fan-out to all targets if only one route exists;
          -- with multiple routes, untagged messages are dropped with a warning.
          let (targetName, payload) = case T.breakOn ":" msg of
                (name, rest) | not (T.null rest) ->
                  (Just name, T.drop 1 rest)
                _ -> (Nothing, msg)
              routeTargets = crClientRoutes routing
          in case targetName of
            Nothing | _:_:_ <- routeTargets ->
              hPutStrLn stderr $ "AgentServer: untagged WS message in multi-route setup, dropping: "
                ++ T.unpack (T.take 80 msg)
            Just tn | tn `notElem` routeTargets ->
              hPutStrLn stderr $ "AgentServer: WS message to unknown route target: "
                ++ T.unpack tn
            _ -> forM_ routeTargets $ \target ->
              case targetName of
                Just tn | tn /= target -> return ()  -- skip non-matching agents
                _ ->
                  case Map.lookup target (crNameMap routing) of
                    Nothing -> return ()
                    Just agent -> do
                      result <- try $ agentStep agent payload
                      case result of
                        Left (e :: IOException) ->
                          hPutStrLn stderr $ "AgentServer: client route step failed for "
                            ++ T.unpack target ++ ": " ++ show e
                        Right output ->
                          applyConnections routing broadcast Set.empty target output
      connClientLoop client routing broadcast
    WS.WsClose -> return ()
