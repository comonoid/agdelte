{-# LANGUAGE OverloadedStrings #-}
-- | Multi-Agent server with HTTP REST + WebSocket push
-- Each Agent is a pure coalgebra (step : S → I → S, observe : S → O)
-- Multiple agents can be registered at different paths
-- WebSocket clients on /ws receive broadcasts on any agent state change
module Agdelte.AgentServer
  ( AgentDef(..)
  , runAgentServer
  ) where

import Control.Concurrent (forkIO)
import Control.Concurrent.STM
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

-- | Run multi-agent server
runAgentServer :: Int -> [AgentDef] -> IO ()
runAgentServer port agents = do
  broadcast <- newBroadcastTChanIO

  -- Build route map
  let routeMap = Map.fromList [(agentPath a, a) | a <- agents]

  putStrLn $ "Agdelte Agent Server on port " ++ show port
  putStrLn $ "  Agents: " ++ show [T.unpack (agentName a) ++ " at " ++ T.unpack (agentPath a) | a <- agents]
  putStrLn "  WebSocket: /ws (broadcasts state changes)"

  Http.serveWithWs port
    (httpHandler routeMap broadcast)
    (Just ("/ws", wsHandler broadcast))

httpHandler :: Map.Map Text AgentDef -> BroadcastChan -> Http.Request -> IO Http.Response
httpHandler routes broadcast req = do
  let path = Http.reqPath req
      body = Http.reqBody req
  -- Parse path: /agent-path/action
  let (agentPath', action) = splitPath path
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

-- | Split "/counter/step" into ("/counter", "step")
splitPath :: Text -> (Text, Text)
splitPath path =
  let parts = filter (not . T.null) (T.splitOn "/" path)
  in case parts of
    []     -> ("/", "")
    [p]    -> ("/" <> p, "state")  -- default to state
    (p:a:_) -> ("/" <> p, a)

wsHandler :: BroadcastChan -> WS.WsConn -> IO ()
wsHandler broadcast conn = do
  -- Each WS client gets its own copy of the broadcast channel
  ch <- atomically $ dupTChan broadcast

  -- Send welcome
  WS.wsSend conn "connected"

  -- Spawn reader thread (to handle ping/pong and close)
  _ <- forkIO $ wsReader conn

  -- Main loop: forward broadcasts to this client
  let loop = do
        msg <- atomically $ readTChan ch
        WS.wsSend conn msg
        loop
  loop

-- | Read from WS client (handle close/ping)
wsReader :: WS.WsConn -> IO ()
wsReader conn = do
  mmsg <- WS.wsReceive conn
  case mmsg of
    Just WS.WsClose -> WS.wsClose conn
    Just _ -> wsReader conn
    Nothing -> return ()  -- connection lost
