{-# LANGUAGE OverloadedStrings #-}
-- | Multi-Agent server with HTTP REST + WebSocket push
-- Each Agent is a pure coalgebra (step : S → I → S, observe : S → O)
-- Multiple agents can be registered at different paths
-- WebSocket clients on /ws receive broadcasts on any agent state change
--
-- Client ID tracking + peek/over protocol for Big Lens
module Agdelte.AgentServer
  ( AgentDef(..)
  , runAgentServer
  ) where

import Control.Concurrent (forkIO)
import Control.Concurrent.STM
import Control.Concurrent.MVar
import qualified Data.IORef as IORef
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Map.Strict as Map

import qualified Agdelte.Http as Http
import qualified Agdelte.WebSocket as WS

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

-- | Client registry: clientId → WsClient
type ClientRegistry = TVar (Map.Map Text WsClient)

-- | Run multi-agent server
runAgentServer :: Int -> [AgentDef] -> IO ()
runAgentServer port agents = do
  broadcast <- newBroadcastTChanIO
  registry  <- newTVarIO Map.empty
  clientCounter <- IORef.newIORef (0 :: Int)

  -- Build route map
  let routeMap = Map.fromList [(agentPath a, a) | a <- agents]

  putStrLn $ "Agdelte Agent Server on port " ++ show port
  putStrLn $ "  Agents: " ++ show [T.unpack (agentName a) ++ " at " ++ T.unpack (agentPath a) | a <- agents]
  putStrLn "  WebSocket: /ws (broadcasts + peek/over protocol)"

  Http.serveWithWs port
    (httpHandler routeMap registry broadcast)
    (Just ("/ws", wsHandler broadcast registry clientCounter))

httpHandler :: Map.Map Text AgentDef -> ClientRegistry -> BroadcastChan -> Http.Request -> IO Http.Response
httpHandler routes registry broadcast req = do
  let path = Http.reqPath req
      body = Http.reqBody req
  -- Parse path: /agent-path/action or /client/clientId/action
  let (agentPath', action) = splitPath path

  -- Client peek/over via HTTP
  case T.stripPrefix "/client/" path of
    Just rest -> handleClientRequest registry rest body
    Nothing ->
      case Map.lookup agentPath' routes of
        Nothing -> return $ Http.Response 404 "Agent not found"
        Just agent -> case action of
          "state" -> do
            output <- agentObserve agent
            return $ Http.Response 200 output
          "step" -> do
            output <- agentStep agent body
            -- Broadcast to WebSocket clients
            let msg = agentName agent <> ":" <> output
            atomically $ writeTChan broadcast msg
            return $ Http.Response 200 output
          _ -> return $ Http.Response 404 "Unknown action (use /state or /step)"

-- | Handle /client/{clientId}/{action} requests
-- GET /client/{clientId}/peek → peek client model via WS
-- POST /client/{clientId}/over → send msg to client via WS
handleClientRequest :: ClientRegistry -> Text -> Text -> IO Http.Response
handleClientRequest registry rest body = do
  let (clientId', action) = case T.breakOn "/" rest of
        (cid, rest') | not (T.null rest') -> (cid, T.drop 1 rest')
        (cid, _) -> (cid, "peek")
  clients <- atomically $ readTVar registry
  case Map.lookup clientId' clients of
    Nothing -> return $ Http.Response 404 ("Client not found: " <> clientId')
    Just client -> case action of
      "peek" -> do
        -- Send peek request to client via WS, wait for response
        WS.wsSend (clientConn client) ("peek:" <> clientId')
        -- Wait for response (client will put it in the MVar)
        response <- takeMVar (clientPendingPeek client)
        return $ Http.Response 200 response
      "over" -> do
        -- Send over (dispatch msg) to client via WS
        WS.wsSend (clientConn client) ("over:" <> body)
        return $ Http.Response 200 "ok"
      _ -> return $ Http.Response 404 "Unknown client action (use /peek or /over)"

-- | Split "/counter/step" into ("/counter", "step")
splitPath :: Text -> (Text, Text)
splitPath path =
  let parts = filter (not . T.null) (T.splitOn "/" path)
  in case parts of
    []     -> ("/", "")
    [p]    -> ("/" <> p, "state")  -- default to state
    (p:a:_) -> ("/" <> p, a)

wsHandler :: BroadcastChan -> ClientRegistry -> IORef.IORef Int -> WS.WsConn -> IO ()
wsHandler broadcast registry counter conn = do
  -- Assign unique client ID
  cid <- IORef.atomicModifyIORef' counter (\n -> (n + 1, n))
  let clientId' = "client-" <> T.pack (show cid)

  -- Create pending peek MVar
  peekMVar <- newEmptyMVar

  let client = WsClient clientId' conn peekMVar

  -- Register client
  atomically $ modifyTVar' registry (Map.insert clientId' client)

  -- Each WS client gets its own copy of the broadcast channel
  ch <- atomically $ dupTChan broadcast

  -- Send welcome with client ID
  WS.wsSend conn ("connected:" <> clientId')

  -- Spawn broadcast reader thread
  _ <- forkIO $ broadcastLoop conn ch

  -- Main loop: read from client (handle peek responses, close, ping)
  clientLoop client registry peekMVar

-- | Forward broadcasts to this client
broadcastLoop :: WS.WsConn -> TChan Text -> IO ()
broadcastLoop conn ch = do
  msg <- atomically $ readTChan ch
  WS.wsSend conn msg
  broadcastLoop conn ch

-- | Read from WS client
clientLoop :: WsClient -> ClientRegistry -> MVar Text -> IO ()
clientLoop client registry peekMVar = do
  mmsg <- WS.wsReceive (clientConn client)
  case mmsg of
    Just WS.WsClose -> do
      -- Unregister client
      atomically $ modifyTVar' registry (Map.delete (clientId client))
      WS.wsClose (clientConn client)
    Just (WS.WsText msg) -> do
      -- Check if this is a peek response
      case T.stripPrefix "peek-response:" msg of
        Just value -> do
          -- Fill the pending peek MVar
          _ <- tryPutMVar peekMVar value
          return ()
        Nothing -> return ()  -- ignore other messages for now
      clientLoop client registry peekMVar
    Just _ -> clientLoop client registry peekMVar
    Nothing -> do
      -- Connection lost — unregister
      atomically $ modifyTVar' registry (Map.delete (clientId client))
