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
  , stopIpcServer
  , connectUnix
  , ipcRequest
  , ipcClose
  -- Agent-specific IPC (ProcessOptic protocol)
  , serveAgentProcess
  , queryProcess
  , stepProcess
  ) where

import Control.Concurrent (ThreadId, forkIO, killThread, myThreadId, threadDelay)
import Control.Concurrent.MVar (MVar, modifyMVar_, newEmptyMVar, newMVar, putMVar, readMVar, swapMVar, takeMVar, withMVar)
import Control.Exception (Exception(..), SomeAsyncException(..), catch, finally, onException, throwIO, SomeException, IOException)
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
import System.Posix.Signals (installHandler, raiseSignal, Handler(..), Signal, sigTERM, sigINT)

------------------------------------------------------------------------
-- IPC Server (agent side)
------------------------------------------------------------------------

-- | IPC server listening on a Unix domain socket
data IpcServer = IpcServer
  { isSocket     :: Socket
  , isPath       :: FilePath
  , isClients    :: MVar [ThreadId]  -- ^ tracked client handler threads
  , isAcceptTid  :: ThreadId         -- ^ accept loop thread
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
      clients <- newMVar []
      -- IORef for accept loop thread (set after forkIO, read by signal handler)
      acceptTidRef <- newIORef Nothing
      -- Clean up socket + file + client threads + accept loop on SIGTERM/SIGINT
      let cleanup = do
            -- Kill accept loop if it's been started
            mAcceptTid <- readIORef acceptTidRef
            case mAcceptTid of
              Just tid -> killThread tid `catch` \(_ :: SomeException) -> return ()
              Nothing  -> return ()
            close sock `catch` \(_ :: SomeException) -> return ()
            threads <- readMVar clients
            mapM_ (\tid -> killThread tid `catch` \(_ :: SomeException) -> return ()) threads
            removeFile path `catch` \(_ :: IOException) -> return ()
      -- Use IORef read lazily inside handler — by the time a signal arrives,
      -- writeIORef has already stored the real previous handler.
      prevTermRef <- newIORef (Catch (return ()))
      prevIntRef  <- newIORef (Catch (return ()))
      oldTerm <- installHandler sigTERM (Catch (cleanup `finally` chainHandler prevTermRef sigTERM)) Nothing
      writeIORef prevTermRef oldTerm
      oldInt  <- installHandler sigINT  (Catch (cleanup `finally` chainHandler prevIntRef sigINT))  Nothing
      writeIORef prevIntRef oldInt
      acceptTid <- forkIO $ acceptLoop sock handler clients
      writeIORef acceptTidRef (Just acceptTid)
      return (IpcServer sock path clients acceptTid)
   ) `onException` close sock

-- | Stop the IPC server: close socket (stops accept loop), cancel client
-- threads, remove socket file. Safe to call on an already-stopped server.
stopIpcServer :: IpcServer -> IO ()
stopIpcServer server = do
  -- Kill accept loop first to stop accepting new connections
  killThread (isAcceptTid server) `catch` \(_ :: SomeException) -> return ()
  -- Close socket
  close (isSocket server) `catch` \(_ :: SomeException) -> return ()
  -- Then kill existing client handlers (swap with [] so re-calling is a no-op)
  threads <- swapMVar (isClients server) []
  mapM_ (\tid -> killThread tid `catch` \(_ :: SomeException) -> return ()) threads
  removeFile (isPath server) `catch` \(_ :: IOException) -> return ()

-- | Invoke a previously-saved signal handler (via IORef).
-- On Default: restore the OS default handler and re-raise the signal,
-- so the process terminates with proper exit status (e.g. 128+signum).
-- Without this, installing a Catch handler would swallow SIGTERM/SIGINT
-- and leave the process running after cleanup.
chainHandler :: IORef Handler -> Signal -> IO ()
chainHandler ref sig = do
  h <- readIORef ref
  case h of
    Catch action -> action
    Default -> do
      _ <- installHandler sig Default Nothing
      raiseSignal sig
    _       -> return ()  -- Ignore: nothing to chain

-- | Accept loop with exception handling.
-- On transient errors (e.g. EMFILE), logs and retries.
-- On fatal errors (e.g. EBADF, resource vanished — socket closed), exits.
acceptLoop :: Socket -> (T.Text -> IO T.Text) -> MVar [ThreadId] -> IO ()
acceptLoop sock handler clients = do
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
          acceptLoop sock handler clients
    Right (conn, _) -> do
      -- Gate ensures the thread is registered before it can deregister.
      -- Without it, a fast-completing handler could try to deregister
      -- before the parent has added its ThreadId to the list.
      gate <- newEmptyMVar
      tid <- forkIO $ do
        myTid <- myThreadId
        takeMVar gate  -- wait for parent to register us
        handleClient conn handler
          `finally` modifyMVar_ clients (return . filter (/= myTid))
      modifyMVar_ clients (\tids -> return (tid : tids))
      putMVar gate ()  -- release the forked thread
      acceptLoop sock handler clients

-- | Check if an IOException is fatal (socket no longer usable).
isFatalSocketError :: IOException -> Bool
isFatalSocketError e = case ioe_type e of
  InvalidArgument     -> True   -- EBADF: socket closed
  ResourceVanished    -> True   -- connection reset / resource gone
  IllegalOperation    -> True   -- socket not in correct state
  _                   -> False  -- EMFILE, ENFILE, etc. are transient

handleClient :: Socket -> (T.Text -> IO T.Text) -> IO ()
handleClient conn handler =
  go `finally` safeClose conn
  where
    go = do
      result <- (Right <$> recvFramed conn) `catch` \(e :: IOException) -> return (Left e)
      case result of
        Left e -> hPutStrLn stderr $ "handleClient: recv error: " ++ show e
        Right Nothing -> return ()  -- clean close by peer
        Right (Just msg) -> do
          let request = TE.decodeUtf8With lenientDecode msg
          response <- handler request `catch` \(e :: SomeException) ->
            case fromException e of
              Just (SomeAsyncException _) -> throwIO e  -- re-raise async exceptions (killThread, cancel)
              Nothing -> return (T.pack $ "error:" ++ show e)
          sendResult <- (Right <$> sendFramed conn (TE.encodeUtf8 response))
            `catch` \(e :: IOException) -> return (Left e)
          case sendResult of
            Left e -> hPutStrLn stderr $ "handleClient: send error: " ++ show e
            Right True -> go
            Right False -> hPutStrLn stderr "handleClient: response too large, closing"

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
-- Returns False if the payload exceeds the 4 GB frame limit (message not sent).
-- Header and payload are sent as two separate sendAll calls to avoid
-- copying the entire payload just to prepend a 4-byte header.
sendFramed :: Socket -> BS.ByteString -> IO Bool
sendFramed sock payload = case encodeLenSafe (BS.length payload) of
  Nothing -> do
    hPutStrLn stderr $ "sendFramed: payload too large (" ++ show (BS.length payload) ++ " bytes), dropping"
    return False
  Just header -> do
    sendAll sock header
    sendAll sock payload
    return True

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
        | len < 0 -> return Nothing  -- invalid (overflow on 32-bit)
        | len == 0 -> return (Just BS.empty)
        | len > maxFrameSize -> do
            hPutStrLn stderr $ "recvFramed: frame too large (" ++ show len ++ " bytes), dropping connection"
            return Nothing
        | otherwise -> recvExact sock len

------------------------------------------------------------------------
-- IPC Client (optic user side)
------------------------------------------------------------------------

-- | IPC client connected to a Unix socket.
-- Thread-safe: concurrent ipcRequest calls are serialized via icLock.
data IpcClient = IpcClient
  { icSocket :: Socket
  , icLock   :: MVar ()
  }

-- | Connect to an agent's Unix socket
connectUnix :: FilePath -> IO IpcClient
connectUnix path = do
  sock <- socket AF_UNIX Stream defaultProtocol
  connect sock (SockAddrUnix path) `onException` close sock
  lock <- newMVar ()
  return (IpcClient sock lock)

-- | Send a request and receive response (length-prefixed framing).
-- Throws IOError if the connection is closed by the peer.
ipcRequest :: IpcClient -> T.Text -> IO T.Text
ipcRequest client request = withMVar (icLock client) $ \_ -> do
  sent <- sendFramed (icSocket client) (TE.encodeUtf8 request)
  if not sent
    then ioError (userError "IPC request too large to send")
    else do
      mResponse <- recvFramed (icSocket client)
      case mResponse of
        Just response -> return (TE.decodeUtf8With lenientDecode response)
        Nothing       -> ioError (userError "IPC connection closed by peer")

-- | Close IPC connection (safe to call on already-closed connections).
-- Re-raises async exceptions (unlike wsClose which is cleanup-only).
ipcClose :: IpcClient -> IO ()
ipcClose client = close (icSocket client) `catch` \(e :: SomeException) ->
  case fromException e of
    Just (SomeAsyncException _) -> throwIO e
    Nothing -> return ()

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
