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
-- Protocol (length-prefixed text frames):
--   Request:  "peek"         → returns current observation
--             "step:INPUT"   → steps agent with INPUT, returns new observation
--   Response: plain text (observation or "error:..." on failure)

module Agdelte.Process
  ( IpcServer
  , IpcClient
  , listenUnix
  , connectUnix
  , ipcRequest
  , ipcClose
  -- Agent-specific IPC (ProcessOptic protocol)
  , serveAgentProcess
  , queryProcess
  , stepProcess
  ) where

import Control.Concurrent (forkIO, threadDelay)
import Control.Exception (catch, finally, onException, SomeException, IOException)
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import GHC.IO.Exception (IOErrorType(..), ioe_type)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Data.Text.Encoding.Error (lenientDecode)
import qualified Data.ByteString as BS
import Data.Bits (shiftL, shiftR, (.&.))
import Data.Word (Word32)
import Network.Socket
import Network.Socket.ByteString (recv, sendAll)
import System.Directory (removeFile)
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
  removeFile path `catch` (\(_ :: IOException) -> return ())
  sock <- socket AF_UNIX Stream defaultProtocol
  (do bind sock (SockAddrUnix path)
      listen sock 5
      -- Clean up socket + file on SIGTERM/SIGINT, chaining previous handlers
      let cleanup = do
            close sock `catch` \(_ :: SomeException) -> return ()
            removeFile path `catch` \(_ :: IOException) -> return ()
      prevTermRef <- newIORef (Catch (return ()))
      prevIntRef  <- newIORef (Catch (return ()))
      oldTerm <- installHandler sigTERM (Catch (cleanup >> chainHandler prevTermRef)) Nothing
      writeIORef prevTermRef oldTerm
      oldInt  <- installHandler sigINT  (Catch (cleanup >> chainHandler prevIntRef))  Nothing
      writeIORef prevIntRef oldInt
      _ <- forkIO $ acceptLoop sock handler
      return (IpcServer sock path)
   ) `onException` close sock

-- | Invoke a previously-saved signal handler (via IORef).
chainHandler :: IORef Handler -> IO ()
chainHandler ref = do
  h <- readIORef ref
  case h of
    Catch action -> action
    _            -> return ()  -- Default/Ignore: nothing to chain

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
        then do
          hPutStrLn stderr "acceptLoop: fatal error, closing socket"
          close sock `catch` \(_ :: SomeException) -> return ()
        else do
          threadDelay 100000  -- 100ms backoff on transient errors
          acceptLoop sock handler
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
handleClient conn handler =
  (go `catch` (\(_ :: IOException) -> return ())) `finally` safeClose conn
  where
    go = do
      result <- (Right <$> recvFramed conn) `catch` \(e :: IOException) -> return (Left e)
      case result of
        Left e -> hPutStrLn stderr $ "handleClient: recv error: " ++ show e
        Right Nothing -> return ()  -- clean close by peer
        Right (Just msg) -> do
          let request = TE.decodeUtf8With lenientDecode msg
          response <- handler request `catch` \(e :: SomeException) ->
            return (T.pack $ "error:" ++ show e)
          sendFramed conn (TE.encodeUtf8 response)
          go

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

-- | Decode a 4-byte big-endian length header (total function)
decodeLen :: BS.ByteString -> Maybe Int
decodeLen bs = case map fromIntegral (BS.unpack bs) of
  [a, b, c, d] -> Just (shiftL (a :: Int) 24 + shiftL b 16 + shiftL c 8 + d)
  _             -> Nothing

-- | Maximum allowed frame size (16 MB). Frames larger than this are rejected
-- to prevent OOM from malicious or corrupted length headers.
maxFrameSize :: Int
maxFrameSize = 16 * 1024 * 1024

-- | Safe close: ignores exceptions from already-closed sockets
safeClose :: Socket -> IO ()
safeClose s = close s `catch` \(_ :: SomeException) -> return ()

-- | Receive exactly n bytes from a socket
recvExact :: Socket -> Int -> IO (Maybe BS.ByteString)
recvExact _ 0 = return (Just BS.empty)
recvExact sock n = go [] n
  where
    go chunks remaining
      | remaining <= 0 = return (Just (BS.concat (reverse chunks)))
      | otherwise = do
          chunk <- recv sock (min remaining 65536)
          if BS.null chunk
            then return Nothing  -- peer closed
            else go (chunk : chunks) (remaining - BS.length chunk)

-- | Send a length-prefixed message.
-- Logs and drops the message if the payload exceeds the 4 GB frame limit.
sendFramed :: Socket -> BS.ByteString -> IO ()
sendFramed sock payload = case encodeLenSafe (BS.length payload) of
  Nothing -> hPutStrLn stderr $ "sendFramed: payload too large (" ++ show (BS.length payload) ++ " bytes), dropping"
  Just header ->
    sendAll sock (header <> payload)

-- | Receive a length-prefixed message.
-- Returns Nothing if the peer closed the connection or frame is invalid/too large.
recvFramed :: Socket -> IO (Maybe BS.ByteString)
recvFramed sock = do
  mHeader <- recvExact sock 4
  case mHeader of
    Nothing -> return Nothing
    Just header -> case decodeLen header of
      Nothing -> return Nothing  -- malformed header
      Just len
        | len == 0 -> return (Just BS.empty)
        | len > maxFrameSize -> do
            hPutStrLn stderr $ "recvFramed: frame too large (" ++ show len ++ " bytes), dropping connection"
            return Nothing
        | otherwise -> recvExact sock len

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
  connect sock (SockAddrUnix path) `onException` close sock
  return (IpcClient sock)

-- | Send a request and receive response (length-prefixed framing).
-- Throws IOError if the connection is closed by the peer.
ipcRequest :: IpcClient -> T.Text -> IO T.Text
ipcRequest client request = do
  sendFramed (icSocket client) (TE.encodeUtf8 request)
  mResponse <- recvFramed (icSocket client)
  case mResponse of
    Just response -> return (TE.decodeUtf8With lenientDecode response)
    Nothing       -> ioError (userError "IPC connection closed by peer")

-- | Close IPC connection (safe to call on already-closed connections)
ipcClose :: IpcClient -> IO ()
ipcClose client = close (icSocket client) `catch` \(_ :: IOException) -> return ()

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
