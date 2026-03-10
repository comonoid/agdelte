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
        -- Drain any stale peek response left from a previous timed-out request
        -- (rec #8: prevents returning outdated data from a previous peek cycle)
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
