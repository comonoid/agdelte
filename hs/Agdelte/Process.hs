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
import Control.Exception (catch, SomeException, bracket, IOException)
import GHC.IO.Exception (IOErrorType(..), ioe_type)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Data.Text.Encoding.Error (lenientDecode)
import qualified Data.ByteString as BS
import Data.Bits (shiftL, shiftR, (.&.))
import Data.Word (Word32)
import Network.Socket
import Network.Socket.ByteString (recv, sendAll)
import System.Directory (removeFile, doesFileExist)
import System.IO (hPutStrLn, stderr)
import System.Posix.Signals (installHandler, Handler(..), sigTERM, sigINT)

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
-- Removes stale socket file if present (avoids "address already in use").
-- Installs signal handlers (SIGTERM, SIGINT) to clean up socket file on exit.
listenUnix :: FilePath -> (T.Text -> IO T.Text) -> IO IpcServer
listenUnix path handler = do
  exists <- doesFileExist path
  if exists then removeFile path else return ()
  sock <- socket AF_UNIX Stream defaultProtocol
  bind sock (SockAddrUnix path)
  listen sock 5
  -- Clean up socket file on SIGTERM/SIGINT
  let cleanup = do
        exists' <- doesFileExist path
        if exists' then removeFile path else return ()
  _ <- installHandler sigTERM (Catch cleanup) Nothing
  _ <- installHandler sigINT  (Catch cleanup) Nothing
  _ <- forkIO $ acceptLoop sock handler
  return (IpcServer sock path)

-- | Accept loop with exception handling.
-- On transient errors (e.g. EMFILE), logs and retries.
-- On fatal errors (e.g. EBADF, resource vanished — socket closed), exits.
acceptLoop :: Socket -> (T.Text -> IO T.Text) -> IO ()
acceptLoop sock handler = do
  result <- (Right <$> accept sock) `catch` \(e :: IOException) -> return (Left e)
  case result of
    Left e -> do
      hPutStrLn stderr $ "acceptLoop: accept failed: " ++ show e
      if isFatalSocketError e
        then hPutStrLn stderr "acceptLoop: fatal error, exiting accept loop"
        else acceptLoop sock handler  -- retry on transient errors
    Right (conn, _) -> do
      _ <- forkIO $ handleClient conn handler
      acceptLoop sock handler

-- | Check if an IOException is fatal (socket no longer usable).
isFatalSocketError :: IOException -> Bool
isFatalSocketError e = case ioe_type e of
  InvalidArgument     -> True   -- EBADF: socket closed
  ResourceVanished    -> True   -- connection reset / resource gone
  IllegalOperation    -> True   -- socket not in correct state
  _                   -> False  -- EMFILE, ENFILE, etc. are transient

handleClient :: Socket -> (T.Text -> IO T.Text) -> IO ()
handleClient conn handler = do
  result <- (Right <$> recvFramed conn) `catch` \(e :: SomeException) -> return (Left e)
  case result of
    Left e -> do
      -- Connection error (not a clean close)
      hPutStrLn stderr $ "handleClient: recv error: " ++ show e
      close conn
    Right Nothing -> close conn  -- clean close by peer
    Right (Just msg) -> do
      let request = TE.decodeUtf8With lenientDecode msg
      response <- handler request `catch` \(e :: SomeException) ->
        return (T.pack $ "error:" ++ show e)
      sendFramed conn (TE.encodeUtf8 response)
      handleClient conn handler

------------------------------------------------------------------------
-- Length-prefix framing: 4-byte big-endian length header + payload
------------------------------------------------------------------------

-- | Encode a 32-bit big-endian length header.
-- Returns Nothing on invalid lengths (negative or exceeds 4 GB).
encodeLenSafe :: Int -> Maybe BS.ByteString
encodeLenSafe n
  | n < 0 = Nothing
  | n > fromIntegral (maxBound :: Word32) = Nothing
  | otherwise = Just $ BS.pack
      [ fromIntegral (shiftR n 24 .&. 0xFF)
      , fromIntegral (shiftR n 16 .&. 0xFF)
      , fromIntegral (shiftR n  8 .&. 0xFF)
      , fromIntegral (         n  .&. 0xFF)
      ]

-- | Decode a 4-byte big-endian length header
decodeLen :: BS.ByteString -> Int
decodeLen bs = case map fromIntegral (BS.unpack bs) of
  [a, b, c, d] -> shiftL (a :: Int) 24 + shiftL b 16 + shiftL c 8 + d
  _             -> error "decodeLen: expected exactly 4 bytes"

-- | Receive exactly n bytes from a socket
recvExact :: Socket -> Int -> IO (Maybe BS.ByteString)
recvExact _ 0 = return (Just BS.empty)
recvExact sock n = go BS.empty n
  where
    go acc remaining
      | remaining <= 0 = return (Just acc)
      | otherwise = do
          chunk <- recv sock (min remaining 65536)
          if BS.null chunk
            then return Nothing  -- peer closed
            else go (acc <> chunk) (remaining - BS.length chunk)

-- | Send a length-prefixed message.
-- Logs and drops the message if the payload exceeds the 4 GB frame limit.
sendFramed :: Socket -> BS.ByteString -> IO ()
sendFramed sock payload = case encodeLenSafe (BS.length payload) of
  Nothing -> hPutStrLn stderr $ "sendFramed: payload too large (" ++ show (BS.length payload) ++ " bytes), dropping"
  Just header -> do
    sendAll sock header
    sendAll sock payload

-- | Receive a length-prefixed message.
-- Returns Nothing if the peer closed the connection.
recvFramed :: Socket -> IO (Maybe BS.ByteString)
recvFramed sock = do
  mHeader <- recvExact sock 4
  case mHeader of
    Nothing -> return Nothing
    Just header -> do
          let len = decodeLen header
          if len == 0
            then return (Just BS.empty)
            else recvExact sock len

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

-- | Send a request and receive response (length-prefixed framing)
ipcRequest :: IpcClient -> T.Text -> IO T.Text
ipcRequest client request = do
  sendFramed (icSocket client) (TE.encodeUtf8 request)
  mResponse <- recvFramed (icSocket client)
  case mResponse of
    Just response -> return (TE.decodeUtf8With lenientDecode response)
    Nothing       -> return "error:connection closed"

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
