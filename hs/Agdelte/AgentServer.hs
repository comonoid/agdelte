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
  ) where

import Control.Concurrent.Async (race_)
import Control.Concurrent.STM
import Control.Concurrent.MVar
import Control.Exception (SomeException, bracket_, try)
import System.IO (hPutStrLn, stderr)
import qualified Data.IORef as IORef
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as Map
import System.Timeout (timeout)
import qualified Data.Set as Set
import Control.Monad (when, forM_)

import qualified Network.Wai as Wai
import qualified Network.Wai.Handler.Warp as Warp

import qualified Agdelte.Http as Http
import qualified Agdelte.WebSocket as WS
import qualified Network.WebSockets as NWS

-- | Agent definition: name, initial state, observe, step
data AgentDef = AgentDef
  { agentName    :: Text
  , agentPath    :: Text                      -- e.g. "/counter"
  , agentState   :: IORef.IORef Text          -- current serialized state
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
  , clientPendingPeek :: MVar Text  -- response slot for peek requests
  }

-- | Client registry: clientId -> WsClient
type ClientRegistry = TVar (Map.Map Text WsClient)

-- | Build a WAI Application from agents and CORS config.
-- Allocates broadcast channel, client registry, and counter internally.
-- Useful for testing (Warp.testWithApplication) without starting a server.
mkAgentApp :: Maybe Text -> [AgentDef] -> IO Wai.Application
mkAgentApp corsOrigin agents = do
  broadcast <- newBroadcastTChanIO
  registry  <- newTVarIO Map.empty
  clientCounter <- IORef.newIORef (0 :: Int)
  let routeMap = Map.fromList [(agentPath a, a) | a <- agents]
  return $ Http.mkApp
    (httpHandler corsOrigin routeMap registry broadcast)
    (Just ("/ws", wsHandler broadcast registry clientCounter))

-- | Run multi-agent server
runAgentServer :: Int -> Maybe Text -> [AgentDef] -> IO ()
runAgentServer port corsOrigin agents = do
  putStrLn $ "Agdelte Agent Server on port " ++ show port
  putStrLn $ "  Agents: " ++ show [T.unpack (agentName a) ++ " at " ++ T.unpack (agentPath a) | a <- agents]
  putStrLn "  WebSocket: /ws (broadcasts + peek/over protocol)"

  app <- mkAgentApp corsOrigin agents
  Warp.runSettings settings app
  where
    settings = Warp.setPort port $ Warp.setHost "*" $ Warp.defaultSettings

httpHandler :: Maybe Text -> Map.Map Text AgentDef -> ClientRegistry -> BroadcastChan -> Http.Request -> IO Http.Response
httpHandler corsOrigin routes registry broadcast req
  | Http.reqMethod req == "OPTIONS" = return $ addCorsHeaders corsOrigin (Http.Response 200 T.empty [])
  | otherwise = do
      let method = Http.reqMethod req
          path = Http.reqPath req
          body = Http.reqBody req
      resp <- routeRequest routes registry broadcast method path body
      return $ addCorsHeaders corsOrigin resp

routeRequest :: Map.Map Text AgentDef -> ClientRegistry -> BroadcastChan -> Text -> Text -> Text -> IO Http.Response
routeRequest routes registry broadcast method path body = do
  -- Parse path: /agent-path/action or /client/clientId/action
  let (agentPath', action) = splitPath path

  -- Client peek/over via HTTP
  case T.stripPrefix "/client/" path of
    Just rest -> handleClientRequest registry rest body
    Nothing ->
      case Map.lookup agentPath' routes of
        Nothing -> return $ Http.Response 404 "Agent not found" []
        Just agent -> case action of
          "state"
            | method == "POST" -> return $ Http.Response 405 "Use GET for /state" []
            | otherwise -> do
                output <- agentObserve agent
                return $ Http.Response 200 output []
          "step"
            | method == "GET" -> return $ Http.Response 405 "Use POST for /step" []
            | otherwise -> do
                output <- agentStep agent body
                -- Broadcast to WebSocket clients
                let msg = agentName agent <> ":" <> output
                atomically $ writeTChan broadcast msg
                return $ Http.Response 200 output []
          _ -> return $ Http.Response 404 "Unknown action (use /state or /step)" []

addCorsHeaders :: Maybe Text -> Http.Response -> Http.Response
addCorsHeaders Nothing resp = resp
addCorsHeaders (Just origin) resp = resp { Http.resHeaders = Http.resHeaders resp ++
  [ ("Access-Control-Allow-Origin", origin)
  , ("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
  , ("Access-Control-Allow-Headers", "Content-Type")
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
        -- Drain any stale peek response left from a previous timed-out request.
        -- NOTE: small race window remains — if the client sends a stale response
        -- between this drain and the new peek, we may return outdated data.
        -- Full fix: add nonce to peek protocol (peek:clientId:nonce → peek-response:nonce:value).
        _ <- tryTakeMVar (clientPendingPeek client)
        result <- try $ WS.wsSend (clientConn client) ("peek:" <> clientId')
        case result of
          Left (_ :: SomeException) ->
            return $ Http.Response 502 "Client disconnected" []
          Right () -> do
            mResponse <- timeout 5000000 $ takeMVar (clientPendingPeek client)
            case mResponse of
              Just response -> return $ Http.Response 200 response []
              Nothing       -> return $ Http.Response 504 "Client peek timeout" []
      "over" -> do
        result <- try $ WS.wsSend (clientConn client) ("over:" <> body)
        case result of
          Left (_ :: SomeException) ->
            return $ Http.Response 502 "Client disconnected" []
          Right () ->
            return $ Http.Response 200 "ok" []
      _ -> return $ Http.Response 404 "Unknown client action (use /peek or /over)" []

-- | Split "/counter/step" into ("/counter", "step")
splitPath :: Text -> (Text, Text)
splitPath path =
  let parts = filter (not . T.null) (T.splitOn "/" path)
  in case parts of
    []     -> ("/", "")
    [p]    -> ("/" <> p, "state")  -- default to state
    (p:a:_) -> ("/" <> p, a)

wsHandler :: BroadcastChan -> ClientRegistry -> IORef.IORef Int -> NWS.PendingConnection -> IO ()
wsHandler broadcast registry counter pending = do
  result <- try $ NWS.acceptRequest pending
  case result of
    Left (_ :: SomeException) -> return ()  -- bad handshake, ignore
    Right conn -> do
      cid <- IORef.atomicModifyIORef' counter (\n -> (n + 1, n))
      let clientId' = "client-" <> T.pack (show cid)
      wsHandlerBody broadcast registry clientId' (WS.WsConn conn)

wsHandlerBody :: BroadcastChan -> ClientRegistry -> Text -> WS.WsConn -> IO ()
wsHandlerBody broadcast registry clientId' conn = do
  peekMVar <- newEmptyMVar
  let client = WsClient clientId' conn peekMVar
  ch <- atomically $ dupTChan broadcast
  bracket_
    (atomically $ modifyTVar' registry (Map.insert clientId' client))
    (do atomically $ modifyTVar' registry (Map.delete clientId')
        _ <- try $ WS.wsClose conn :: IO (Either SomeException ())
        return ())
    (do WS.wsSend conn ("connected:" <> clientId')
        race_ (broadcastLoop conn ch) (clientLoop client))

-- | Forward broadcasts to this client.
-- Catches send exceptions silently — if the connection is gone, the loop
-- exits and race_ cancels clientLoop (rec #16, #19).
broadcastLoop :: WS.WsConn -> TChan Text -> IO ()
broadcastLoop conn ch = do
  msg <- atomically $ readTChan ch
  result <- try $ WS.wsSend conn msg
  case result of
    Left (_ :: SomeException) -> return ()  -- connection gone, exit cleanly
    Right () -> broadcastLoop conn ch

-- | Read from WS client
clientLoop :: WsClient -> IO ()
clientLoop client = do
  mmsg <- WS.wsReceive (clientConn client)
  case mmsg of
    Just (WS.WsText msg) -> do
      case T.stripPrefix "peek-response:" msg of
        Just value -> do
          ok <- tryPutMVar (clientPendingPeek client) value
          if ok then return ()
                else hPutStrLn stderr $ "AgentServer: peek response dropped for "
                       ++ T.unpack (clientId client) ++ " (previous response not consumed)"
        Nothing -> return ()
      clientLoop client
    _ -> return ()  -- WsClose or connection error — bracket_ cleanup handles unregister + close

------------------------------------------------------------------------
-- Connection-aware server (Diagram routing)
------------------------------------------------------------------------

-- | Apply connection routing after an agent step.
-- Handles broadcast to WS, agent pipes (with cycle detection).
applyConnections :: Map.Map Text AgentDef -> [ConnectionDef] -> BroadcastChan
                 -> Set.Set Text -> Text -> Text -> IO ()
applyConnections nameMap conns broadcast visited source output
  | Set.member source visited = return ()  -- cycle detected, stop
  | otherwise = do
      let visited' = Set.insert source visited
      -- Broadcast to WS clients if declared
      when (any isBroadcastFor conns) $
        atomically $ writeTChan broadcast (source <> ":" <> output)
      -- Pipe to target agents (each pipe is independently exception-safe)
      forM_ [t | AgentPipeDef s t <- conns, s == source] $ \target ->
        case Map.lookup target nameMap of
          Nothing -> hPutStrLn stderr $
            "AgentServer: pipe target not found: " ++ T.unpack target
          Just targetAgent -> do
            result <- try $ agentStep targetAgent output
            case result of
              Left (e :: SomeException) ->
                hPutStrLn stderr $ "AgentServer: pipe step failed for "
                  ++ T.unpack target ++ ": " ++ show e
              Right targetOutput ->
                applyConnections nameMap conns broadcast visited' target targetOutput
  where
    isBroadcastFor (BroadcastDef n) = n == source
    isBroadcastFor _                = False

-- | Run multi-agent server with connection routing
runAgentServerWithConns :: Int -> Maybe Text -> [AgentDef] -> [ConnectionDef] -> IO ()
runAgentServerWithConns port corsOrigin agents conns = do
  putStrLn $ "Agdelte Agent Server on port " ++ show port
  putStrLn $ "  Agents: " ++ show [T.unpack (agentName a) ++ " at " ++ T.unpack (agentPath a) | a <- agents]
  putStrLn $ "  Connections: " ++ show (length conns)
  putStrLn "  WebSocket: /ws (connection routing active)"

  broadcast <- newBroadcastTChanIO
  registry  <- newTVarIO Map.empty
  clientCounter <- IORef.newIORef (0 :: Int)
  let routeMap = Map.fromList [(agentPath a, a) | a <- agents]
      nameMap  = Map.fromList [(agentName a, a) | a <- agents]
      app = Http.mkApp
        (connHttpHandler corsOrigin routeMap nameMap conns registry broadcast)
        (Just ("/ws", connWsHandler broadcast registry clientCounter nameMap conns))
  Warp.runSettings settings app
  where
    settings = Warp.setPort port $ Warp.setHost "*" $ Warp.defaultSettings

connHttpHandler :: Maybe Text -> Map.Map Text AgentDef -> Map.Map Text AgentDef
               -> [ConnectionDef] -> ClientRegistry -> BroadcastChan
               -> Http.Request -> IO Http.Response
connHttpHandler corsOrigin routes nameMap conns registry broadcast req
  | Http.reqMethod req == "OPTIONS" = return $ addCorsHeaders corsOrigin (Http.Response 200 T.empty [])
  | otherwise = do
      let method = Http.reqMethod req
          path = Http.reqPath req
          body = Http.reqBody req
      resp <- connRouteRequest routes nameMap conns registry broadcast method path body
      return $ addCorsHeaders corsOrigin resp

connRouteRequest :: Map.Map Text AgentDef -> Map.Map Text AgentDef
                -> [ConnectionDef] -> ClientRegistry -> BroadcastChan
                -> Text -> Text -> Text -> IO Http.Response
connRouteRequest routes nameMap conns registry broadcast method path body = do
  let (agentPath', action) = splitPath path
  case T.stripPrefix "/client/" path of
    Just rest -> handleClientRequest registry rest body
    Nothing ->
      case Map.lookup agentPath' routes of
        Nothing -> return $ Http.Response 404 "Agent not found" []
        Just agent -> case action of
          "state"
            | method == "POST" -> return $ Http.Response 405 "Use GET for /state" []
            | otherwise -> do
                output <- agentObserve agent
                return $ Http.Response 200 output []
          "step"
            | method == "GET" -> return $ Http.Response 405 "Use POST for /step" []
            | otherwise -> do
                output <- agentStep agent body
                -- Apply connection routing (broadcast + pipes)
                applyConnections nameMap conns broadcast Set.empty (agentName agent) output
                return $ Http.Response 200 output []
          _ -> return $ Http.Response 404 "Unknown action (use /state or /step)" []

connWsHandler :: BroadcastChan -> ClientRegistry -> IORef.IORef Int
             -> Map.Map Text AgentDef -> [ConnectionDef]
             -> NWS.PendingConnection -> IO ()
connWsHandler broadcast registry counter nameMap conns pending = do
  result <- try $ NWS.acceptRequest pending
  case result of
    Left (_ :: SomeException) -> return ()
    Right conn -> do
      cid <- IORef.atomicModifyIORef' counter (\n -> (n + 1, n))
      let clientId' = "client-" <> T.pack (show cid)
      connWsHandlerBody broadcast registry clientId' (WS.WsConn conn) nameMap conns

connWsHandlerBody :: BroadcastChan -> ClientRegistry -> Text -> WS.WsConn
                 -> Map.Map Text AgentDef -> [ConnectionDef] -> IO ()
connWsHandlerBody broadcast registry clientId' conn nameMap conns = do
  peekMVar <- newEmptyMVar
  let client = WsClient clientId' conn peekMVar
  ch <- atomically $ dupTChan broadcast
  bracket_
    (atomically $ modifyTVar' registry (Map.insert clientId' client))
    (do atomically $ modifyTVar' registry (Map.delete clientId')
        _ <- try $ WS.wsClose conn :: IO (Either SomeException ())
        return ())
    (do WS.wsSend conn ("connected:" <> clientId')
        race_ (broadcastLoop conn ch) (connClientLoop client nameMap conns broadcast))

-- | Connection-aware client loop: routes WS messages via ClientRouteDef
connClientLoop :: WsClient -> Map.Map Text AgentDef -> [ConnectionDef] -> BroadcastChan -> IO ()
connClientLoop client nameMap conns broadcast = do
  mmsg <- WS.wsReceive (clientConn client)
  case mmsg of
    Just (WS.WsText msg) -> do
      case T.stripPrefix "peek-response:" msg of
        Just value -> do
          ok <- tryPutMVar (clientPendingPeek client) value
          if ok then return ()
                else hPutStrLn stderr $ "AgentServer: peek response dropped for "
                       ++ T.unpack (clientId client) ++ " (previous response not consumed)"
        Nothing ->
          -- Route client message to agents via ClientRouteDef.
          -- Message format: "agentName:payload" routes to specific agent.
          -- Untagged messages (no colon) fan-out to all ClientRouteDef agents.
          let (targetName, payload) = case T.breakOn ":" msg of
                (name, rest) | not (T.null rest) ->
                  (Just name, T.drop 1 rest)
                _ -> (Nothing, msg)
              routeTargets = [n | ClientRouteDef n <- conns]
          in forM_ routeTargets $ \target ->
            case targetName of
              Just tn | tn /= target -> return ()  -- skip non-matching agents
              _ ->
                case Map.lookup target nameMap of
                  Nothing -> return ()
                  Just agent -> do
                    result <- try $ agentStep agent payload
                    case result of
                      Left (e :: SomeException) ->
                        hPutStrLn stderr $ "AgentServer: client route step failed for "
                          ++ T.unpack target ++ ": " ++ show e
                      Right output ->
                        applyConnections nameMap conns broadcast Set.empty target output
      connClientLoop client nameMap conns broadcast
    _ -> return ()
