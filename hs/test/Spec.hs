{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import Test.Hspec

import qualified Numeric
import Control.Concurrent (threadDelay)
import Control.Concurrent.Async (async, cancel, mapConcurrently)
import Control.Concurrent.MVar
import Control.Exception (SomeException, bracket, try)
import Data.IORef
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.ByteString as BS
import qualified Network.Socket as NS
import qualified Network.Socket.ByteString as NSB
import qualified Network.Wai as Wai
import qualified Network.Wai.Handler.Warp as Warp
import qualified Network.WebSockets as WS

import qualified Agdelte.Http as Http
import qualified Agdelte.AgentServer as Agent
import qualified Agdelte.Process as Process

-- Helper: run a WAI app on an ephemeral port and pass port to callback
withApp :: Wai.Application -> (Int -> IO a) -> IO a
withApp app = Warp.testWithApplication (return app)

-- Helper: connect raw TCP to localhost:port
connectRaw :: Int -> IO NS.Socket
connectRaw port = do
  let hints = NS.defaultHints { NS.addrSocketType = NS.Stream }
  addrs <- NS.getAddrInfo (Just hints) (Just "127.0.0.1") (Just (show port))
  addr <- case addrs of
    (a:_) -> return a
    []    -> fail $ "getAddrInfo returned no results for port " ++ show port
  sock <- NS.openSocket addr
  NS.connect sock (NS.addrAddress addr)
  return sock

-- Helper: receive all data until connection closes
recvAllBS :: NS.Socket -> IO BS.ByteString
recvAllBS sock = go []
  where
    go chunks = do
      chunk <- NSB.recv sock 65536
      if BS.null chunk
        then return (BS.concat (reverse chunks))
        else go (chunk : chunks)

-- Parse raw HTTP response into (status, body, headers)
parseHttpResponse :: BS.ByteString -> (Int, BS.ByteString, [(BS.ByteString, BS.ByteString)])
parseHttpResponse raw =
  let (headerPart, rest) = BS.breakSubstring "\r\n\r\n" raw
      rawBody = BS.drop 4 rest  -- drop \r\n\r\n
      headerLines = map stripCR (BS.split 0x0A headerPart)
      statusCode = case headerLines of
        (statusLine:_) ->
          let parts = BS.split 0x20 statusLine
          in case parts of
            (_:code:_) -> case reads (map (toEnum . fromIntegral) (BS.unpack code)) of
              [(n, _)] -> n
              _ -> 0
            _ -> 0
        _ -> 0
      hdrs = [ (k, BS.drop 2 v)
             | l <- drop 1 headerLines
             , let (k, v) = BS.breakSubstring ": " l
             , not (BS.null v)
             ]
      isChunked = any (\(k, v) -> eqCI k "Transfer-Encoding" && BS.isInfixOf "chunked" v) hdrs
      body = if isChunked then dechunk rawBody else rawBody
  in (statusCode, body, hdrs)
  where
    stripCR bs | not (BS.null bs) && BS.last bs == 0x0D = BS.init bs
               | otherwise = bs
    eqCI a b = BS.map toLowerW8 a == BS.map toLowerW8 b
    toLowerW8 w | w >= 0x41 && w <= 0x5A = w + 0x20
                | otherwise = w

-- Decode chunked transfer-encoding body
dechunk :: BS.ByteString -> BS.ByteString
dechunk bs = BS.concat (reverse (go bs []))
  where
    go remaining chunks =
      let (sizeLine, rest) = BS.breakSubstring "\r\n" remaining
          rest' = BS.drop 2 rest  -- skip \r\n after size
      in case Numeric.readHex (map (toEnum . fromIntegral) (BS.unpack sizeLine)) of
          [(0, _)] -> chunks
          [(n, _)] ->
            let chunk = BS.take n rest'
                rest'' = BS.drop (n + 2) rest'  -- skip chunk + \r\n
            in go rest'' (chunk : chunks)
          _ -> chunks


-- Helper: simple HTTP GET via raw sockets
httpGet :: Int -> String -> IO (Int, BS.ByteString, [(BS.ByteString, BS.ByteString)])
httpGet port path =
  bracket (connectRaw port) NS.close $ \sock -> do
    let reqBS = BS.concat
          [ "GET ", TE.encodeUtf8 (T.pack path), " HTTP/1.1\r\n"
          , "Host: localhost:", TE.encodeUtf8 (T.pack (show port)), "\r\n"
          , "Connection: close\r\n"
          , "\r\n"
          ]
    NSB.sendAll sock reqBS
    resp <- recvAllBS sock
    return (parseHttpResponse resp)

-- Helper: HTTP POST
httpPost :: Int -> String -> Text -> IO (Int, BS.ByteString, [(BS.ByteString, BS.ByteString)])
httpPost port path body =
  bracket (connectRaw port) NS.close $ \sock -> do
    let bodyBS = TE.encodeUtf8 body
    let reqBS = BS.concat
          [ "POST ", TE.encodeUtf8 (T.pack path), " HTTP/1.1\r\n"
          , "Host: localhost:", TE.encodeUtf8 (T.pack (show port)), "\r\n"
          , "Content-Type: application/json\r\n"
          , "Content-Length: ", TE.encodeUtf8 (T.pack (show (BS.length bodyBS))), "\r\n"
          , "Connection: close\r\n"
          , "\r\n"
          , bodyBS
          ]
    NSB.sendAll sock reqBS
    resp <- recvAllBS sock
    return (parseHttpResponse resp)

main :: IO ()
main = hspec $ do
  describe "Http" httpTests
  describe "WebSocket" wsTests
  describe "AgentServer" agentTests
  describe "Process timeout" processTimeoutTests
  describe "AgentServer concurrent access" concurrentAgentTests

-- | Simple echo HTTP handler for tests
testHttpHandler :: Http.Request -> IO Http.Response
testHttpHandler req =
  case Http.reqPath req of
    "/echo"  -> return $ Http.Response 200 (Http.reqBody req) []
    "/state" -> return $ Http.Response 200 "hello" []
    "/html"  -> return $ Http.Response 200 "<h1>hi</h1>" [("Content-Type", "text/html")]
    _        -> return $ Http.Response 404 "not found" []

httpTests :: Spec
httpTests = do
  it "GET /state returns 200 with body" $ do
    withApp (Http.toWaiApp testHttpHandler) $ \port -> do
      (status, body, _) <- httpGet port "/state"
      status `shouldBe` 200
      body `shouldBe` "hello"

  it "POST /echo returns posted body" $ do
    withApp (Http.toWaiApp testHttpHandler) $ \port -> do
      (status, body, _) <- httpPost port "/echo" "test-body"
      status `shouldBe` 200
      body `shouldBe` "test-body"

  it "POST with body > 65KB arrives completely" $ do
    withApp (Http.toWaiApp testHttpHandler) $ \port -> do
      let bigBody = T.replicate 70000 "x"
      (status, body, _) <- httpPost port "/echo" bigBody
      status `shouldBe` 200
      BS.length body `shouldBe` 70000

  it "COOP/COEP headers are present" $ do
    withApp (Http.toWaiApp testHttpHandler) $ \port -> do
      (_, _, hdrs) <- httpGet port "/state"
      lookup "Cross-Origin-Opener-Policy" hdrs `shouldBe` Just "same-origin"
      lookup "Cross-Origin-Embedder-Policy" hdrs `shouldBe` Just "require-corp"

  it "custom Content-Type is not overridden" $ do
    withApp (Http.toWaiApp testHttpHandler) $ \port -> do
      (_, _, hdrs) <- httpGet port "/html"
      let ctHeaders = filter (\(k, _) -> k == "Content-Type" || k == "content-type") hdrs
      length ctHeaders `shouldBe` 1

  it "404 for unknown path" $ do
    withApp (Http.toWaiApp testHttpHandler) $ \port -> do
      (status, _, _) <- httpGet port "/nonexistent"
      status `shouldBe` 404

wsTests :: Spec
wsTests = do
  it "connects, sends text, receives response" $ do
    let wsApp pending = do
          conn <- WS.acceptRequest pending
          msg <- WS.receiveData conn :: IO Text
          WS.sendTextData conn ("echo:" <> msg)
        app = Http.mkApp testHttpHandler (Just ("/ws", wsApp))
    withApp app $ \port -> do
      WS.runClient "127.0.0.1" port "/ws" $ \conn -> do
        WS.sendTextData conn ("hello" :: Text)
        msg <- WS.receiveData conn :: IO Text
        msg `shouldBe` "echo:hello"

  it "frame > 65KB arrives intact" $ do
    let wsApp pending = do
          conn <- WS.acceptRequest pending
          msg <- WS.receiveData conn :: IO Text
          WS.sendTextData conn msg
        app = Http.mkApp testHttpHandler (Just ("/ws", wsApp))
    withApp app $ \port -> do
      WS.runClient "127.0.0.1" port "/ws" $ \conn -> do
        let bigMsg = T.replicate 70000 "y"
        WS.sendTextData conn bigMsg
        msg <- WS.receiveData conn :: IO Text
        T.length msg `shouldBe` 70000

  it "close frame results in clean shutdown" $ do
    closedMVar <- newEmptyMVar
    let wsApp pending = do
          conn <- WS.acceptRequest pending
          result <- try $ WS.receiveDataMessage conn :: IO (Either WS.ConnectionException WS.DataMessage)
          case result of
            Left _ -> putMVar closedMVar True
            Right _ -> putMVar closedMVar False
        app = Http.mkApp testHttpHandler (Just ("/ws", wsApp))
    withApp app $ \port -> do
      WS.runClient "127.0.0.1" port "/ws" $ \conn ->
        WS.sendClose conn ("bye" :: Text)
      closed <- takeMVar closedMVar
      closed `shouldBe` True

  it "disconnect without close frame does not crash server" $ do
    let wsApp pending = do
          conn <- WS.acceptRequest pending
          _ <- try $ WS.receiveDataMessage conn :: IO (Either SomeException WS.DataMessage)
          return ()
        app = Http.mkApp testHttpHandler (Just ("/ws", wsApp))
    withApp app $ \port -> do
      -- Connect via raw socket, send upgrade, wait for response, then close abruptly
      bracket (connectRaw port) NS.close $ \sock -> do
        let req = BS.concat
              [ "GET /ws HTTP/1.1\r\n"
              , "Host: localhost\r\n"
              , "Upgrade: websocket\r\n"
              , "Connection: Upgrade\r\n"
              , "Sec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ==\r\n"
              , "Sec-WebSocket-Version: 13\r\n"
              , "\r\n"
              ]
        NSB.sendAll sock req
        -- Wait for upgrade response before closing abruptly
        _ <- NSB.recv sock 4096
        return ()
      -- Server should still work after abrupt disconnect
      (status, _, _) <- httpGet port "/state"
      status `shouldBe` 200

-- Agent tests: simple counter agent
agentTests :: Spec
agentTests = do
  it "GET /counter/state returns initial state" $ do
    withAgentServer $ \port -> do
      (status, body, _) <- httpGet port "/counter/state"
      status `shouldBe` 200
      body `shouldBe` "0"

  it "POST /counter/step increments and returns new state" $ do
    withAgentServer $ \port -> do
      (status1, body1, _) <- httpPost port "/counter/step" ""
      status1 `shouldBe` 200
      body1 `shouldBe` "1"
      (status2, body2, _) <- httpGet port "/counter/state"
      status2 `shouldBe` 200
      body2 `shouldBe` "1"

  it "WS client receives broadcast on step" $ do
    withAgentServer $ \port -> do
      gotBroadcast <- newEmptyMVar
      wsThread <- async $
        WS.runClient "127.0.0.1" port "/ws" $ \conn -> do
          welcome <- WS.receiveData conn :: IO Text
          putMVar gotBroadcast ("welcome", welcome)
          msg <- WS.receiveData conn :: IO Text
          putMVar gotBroadcast ("broadcast", msg)

      (tag1, welcomeMsg) <- takeMVar gotBroadcast
      tag1 `shouldBe` ("welcome" :: Text)
      welcomeMsg `shouldSatisfy` T.isPrefixOf "connected:"

      (status, _, _) <- httpPost port "/counter/step" ""
      status `shouldBe` 200

      (tag2, broadcastMsg) <- takeMVar gotBroadcast
      tag2 `shouldBe` ("broadcast" :: Text)
      broadcastMsg `shouldSatisfy` T.isPrefixOf "counter:"

      cancel wsThread

  it "CORS headers present when origin configured" $ do
    withAgentServerCors (Just "http://localhost:3000") $ \port -> do
      (_, _, hdrs) <- httpGet port "/counter/state"
      lookup "Access-Control-Allow-Origin" hdrs `shouldBe` Just "http://localhost:3000"

-- Build a test counter agent as a WAI app on ephemeral port
-- Uses AgentServer.mkAgentApp directly — no duplicated routing/WS logic
withAgentServer :: (Int -> IO a) -> IO a
withAgentServer = withAgentServerCors Nothing

withAgentServerCors :: Maybe Text -> (Int -> IO a) -> IO a
withAgentServerCors corsOrigin action = do
  stateRef <- newIORef (0 :: Int)
  let observe = do  -- readIORef is atomic for single-word reads on GHC
        n <- readIORef stateRef
        return (T.pack (show n))
      step _ = do
        n <- atomicModifyIORef' stateRef (\n' -> (n' + 1, n' + 1))
        return (T.pack (show n))
  let agent = Agent.AgentDef
        { Agent.agentName = "counter"
        , Agent.agentPath = "/counter"
        , Agent.agentObserve = observe
        , Agent.agentStep = step
        }
  app <- Agent.mkAgentApp corsOrigin [agent]
  withApp app action

------------------------------------------------------------------------
-- Process timeout tests (H2)
------------------------------------------------------------------------

-- | Helper: run an IPC server on a temp Unix socket, connect a client,
-- run the test, then clean up both sides.
withIpc :: FilePath -> IO T.Text -> (T.Text -> IO T.Text)
        -> (Process.IpcClient -> IO a) -> IO a
withIpc path observe step action =
  bracket (Process.serveAgentProcess path observe step) Process.stopIpcServer $ \_ -> do
    -- Small delay to let the accept loop start
    threadDelay 50000
    bracket (Process.connectUnix path) Process.ipcClose action

processTimeoutTests :: Spec
processTimeoutTests = do
  it "fast peek completes successfully within timeout" $ do
    ref <- newIORef ("hello" :: T.Text)
    let observe = readIORef ref
        step _  = atomicModifyIORef' ref (\s -> (s <> "!", s <> "!"))
        path = "/tmp/agdelte-test-timeout-fast.sock"
    withIpc path observe step $ \client -> do
      result <- Process.queryProcess client
      result `shouldBe` "hello"

  it "fast step completes successfully within timeout" $ do
    ref <- newIORef ("0" :: T.Text)
    let observe = readIORef ref
        step input = do
          let new = input <> "-ok"
          writeIORef ref new
          return new
        path = "/tmp/agdelte-test-timeout-step.sock"
    withIpc path observe step $ \client -> do
      result <- Process.stepProcess client "test"
      result `shouldBe` "test-ok"
      -- Verify the state was updated
      state <- Process.queryProcess client
      state `shouldBe` "test-ok"

  it "handler exception returns error response (not crash)" $ do
    let observe = return "ok" :: IO T.Text
        step _ = error "intentional test error"
        path = "/tmp/agdelte-test-timeout-err.sock"
    withIpc path observe step $ \client -> do
      result <- Process.stepProcess client "boom"
      -- The handler catches exceptions and returns "error:..." text
      T.isPrefixOf "error:" result `shouldBe` True

  -- Note: testing the actual 30-second timeout would require waiting 30+ seconds.
  -- The timeout is hardcoded in Process.handleClient. The tests above verify that
  -- the timeout wrapper does not interfere with normal (fast) operations, and that
  -- exceptions are caught correctly — the same code path that timeout uses.

------------------------------------------------------------------------
-- Concurrent access tests (H6)
------------------------------------------------------------------------

concurrentAgentTests :: Spec
concurrentAgentTests = do
  it "concurrent GET /counter/state requests all succeed" $ do
    withAgentServer $ \port -> do
      -- Fire 20 concurrent GET requests
      results <- mapConcurrently (\_ -> httpGet port "/counter/state") [(1::Int)..20]
      -- All should return 200 with consistent state
      let statuses = map (\(s, _, _) -> s) results
      all (== 200) statuses `shouldBe` True

  it "concurrent POST /counter/step requests all succeed and produce correct final state" $ do
    withAgentServer $ \port -> do
      -- Fire 50 concurrent step requests
      results <- mapConcurrently (\_ -> httpPost port "/counter/step" "") [(1::Int)..50]
      let statuses = map (\(s, _, _) -> s) results
      all (== 200) statuses `shouldBe` True
      -- Each step increments by 1, so final state should be 50
      (_, finalBody, _) <- httpGet port "/counter/state"
      finalBody `shouldBe` "50"

  it "concurrent mixed GET and POST requests do not crash or corrupt" $ do
    withAgentServer $ \port -> do
      -- Mix of reads and writes concurrently
      let actions = [ if even i
                      then httpGet port "/counter/state"
                      else httpPost port "/counter/step" ""
                    | i <- [(1::Int)..40]
                    ]
      results <- mapConcurrently id actions
      let statuses = map (\(s, _, _) -> s) results
      -- No 500s or other error codes
      all (== 200) statuses `shouldBe` True
      -- The number of steps is the number of odd indices in [1..40] = 20
      (_, finalBody, _) <- httpGet port "/counter/state"
      finalBody `shouldBe` "20"

  it "concurrent WebSocket connects + HTTP steps do not crash" $ do
    withAgentServer $ \port -> do
      -- Start 5 WS clients that each listen for one broadcast
      gotMessages <- newMVar (0 :: Int)
      wsThreads <- mapConcurrently (\_ ->
        async $ WS.runClient "127.0.0.1" port "/ws" $ \conn -> do
          -- Read welcome message
          _ <- WS.receiveData conn :: IO Text
          -- Read one broadcast
          _ <- WS.receiveData conn :: IO Text
          modifyMVar_ gotMessages (\n -> return (n + 1))
        ) [(1::Int)..5]
      -- Small delay to let WS clients connect and register
      threadDelay 100000
      -- Step the agent to trigger a broadcast
      (status, _, _) <- httpPost port "/counter/step" ""
      status `shouldBe` 200
      -- Wait a bit for broadcasts to propagate then clean up
      threadDelay 200000
      mapM_ cancel wsThreads
      received <- readMVar gotMessages
      -- At least some WS clients should have received the broadcast
      received `shouldSatisfy` (> 0)
