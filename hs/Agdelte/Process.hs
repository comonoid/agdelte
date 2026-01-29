{-# LANGUAGE OverloadedStrings #-}

-- | Process communication: IPC via Unix domain sockets.
--
-- Provides the transport layer for ProcessOptic — accessing agent state
-- in another OS process using the same peek/over interface as local optics.
--
-- Architecture:
--   Process A (agent server) listens on Unix socket
--   Process B (client) connects and sends optic operations
--   Same Agda types on both sides, serialized via Serialize record
--
-- Protocol:
--   Request:  { "op": "peek" | "over", "path": "...", "payload": "..." }
--   Response: { "status": "ok" | "error", "value": "..." }

module Agdelte.Process
  ( IpcServer(..)
  , IpcClient(..)
  , listenUnix
  , connectUnix
  , ipcRequest
  , ipcClose
  -- Agent-specific IPC (ProcessOptic protocol)
  , serveAgentProcess
  , queryProcess
  , stepProcess
  ) where

import Control.Concurrent (forkIO)
import Control.Exception (bracket, catch, SomeException)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.ByteString as BS
import Network.Socket
import Network.Socket.ByteString (recv, sendAll)

------------------------------------------------------------------------
-- IPC Server (agent side)
------------------------------------------------------------------------

-- | IPC server listening on a Unix domain socket
data IpcServer = IpcServer
  { isSocket :: Socket
  , isPath   :: FilePath
  }

-- | Start listening on a Unix socket path.
-- Handler receives request text, returns response text.
listenUnix :: FilePath -> (T.Text -> IO T.Text) -> IO IpcServer
listenUnix path handler = do
  sock <- socket AF_UNIX Stream defaultProtocol
  bind sock (SockAddrUnix path)
  listen sock 5
  _ <- forkIO $ acceptLoop sock handler
  return (IpcServer sock path)

acceptLoop :: Socket -> (T.Text -> IO T.Text) -> IO ()
acceptLoop sock handler = do
  (conn, _) <- accept sock
  _ <- forkIO $ handleClient conn handler
  acceptLoop sock handler

handleClient :: Socket -> (T.Text -> IO T.Text) -> IO ()
handleClient conn handler = do
  msg <- recv conn 65536
  if BS.null msg
    then close conn
    else do
      let request = TE.decodeUtf8 msg
      response <- handler request `catch` \(e :: SomeException) ->
        return (T.pack $ "error:" ++ show e)
      sendAll conn (TE.encodeUtf8 response)
      handleClient conn handler

------------------------------------------------------------------------
-- IPC Client (optic user side)
------------------------------------------------------------------------

-- | IPC client connected to a Unix socket
data IpcClient = IpcClient
  { icSocket :: Socket
  }

-- | Connect to an agent's Unix socket
connectUnix :: FilePath -> IO IpcClient
connectUnix path = do
  sock <- socket AF_UNIX Stream defaultProtocol
  connect sock (SockAddrUnix path)
  return (IpcClient sock)

-- | Send a request and receive response
ipcRequest :: IpcClient -> T.Text -> IO T.Text
ipcRequest client request = do
  sendAll (icSocket client) (TE.encodeUtf8 request)
  response <- recv (icSocket client) 65536
  return (TE.decodeUtf8 response)

-- | Close IPC connection
ipcClose :: IpcClient -> IO ()
ipcClose client = close (icSocket client)

------------------------------------------------------------------------
-- Agent-specific IPC (ProcessOptic protocol)
------------------------------------------------------------------------

-- | Serve an agent over Unix socket using ProcessOptic protocol.
-- Protocol:
--   "peek"        → returns current observation
--   "step:INPUT"  → steps agent with INPUT, returns new observation
serveAgentProcess :: FilePath
                  -> IO T.Text              -- ^ observe function
                  -> (T.Text -> IO T.Text)  -- ^ step function
                  -> IO IpcServer
serveAgentProcess path observe step = listenUnix path handler
  where
    handler :: T.Text -> IO T.Text
    handler msg
      | msg == "peek" = observe
      | "step:" `T.isPrefixOf` msg = step (T.drop 5 msg)
      | otherwise = return "error:unknown command"

-- | Query agent state via ProcessOptic (peek)
queryProcess :: IpcClient -> IO T.Text
queryProcess client = ipcRequest client "peek"

-- | Step agent via ProcessOptic (over)
stepProcess :: IpcClient -> T.Text -> IO T.Text
stepProcess client input = ipcRequest client ("step:" <> input)
