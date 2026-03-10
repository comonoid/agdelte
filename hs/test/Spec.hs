{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import Test.Hspec

import Control.Concurrent (threadDelay)
import qualified Numeric
import Control.Concurrent.Async (async, cancel)
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

-- Helper: run a WAI app on an ephemeral port and pass port to callback
withApp :: Wai.Application -> (Int -> IO a) -> IO a
withApp app = Warp.testWithApplication (return app)

-- Helper: connect raw TCP to localhost:port
connectRaw :: Int -> IO NS.Socket
connectRaw port = do
  let hints = NS.defaultHints { NS.addrSocketType = NS.Stream }
  addr:_ <- NS.getAddrInfo (Just hints) (Just "127.0.0.1") (Just (show port))
  sock <- NS.openSocket addr
  NS.connect sock (NS.addrAddress addr)
  return sock

-- Helper: receive all data until connection closes
recvAllBS :: NS.Socket -> IO BS.ByteString
recvAllBS sock = go BS.empty
  where
    go acc = do
      chunk <- NSB.recv sock 65536
      if BS.null chunk
        then return acc
        else go (acc <> chunk)

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
dechunk bs = go bs BS.empty
  where
    go remaining acc =
      let (sizeLine, rest) = BS.breakSubstring "\r\n" remaining
          rest' = BS.drop 2 rest  -- skip \r\n after size
      in case readHex (map (toEnum . fromIntegral) (BS.unpack sizeLine)) of
          [(0, _)] -> acc
          [(n, _)] ->
            let chunk = BS.take n rest'
                rest'' = BS.drop (n + 2) rest'  -- skip chunk + \r\n
            in go rest'' (acc <> chunk)
          _ -> acc

readHex :: String -> [(Int, String)]
readHex s = case Numeric.readHex s of
  [] -> []
  xs -> xs

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
    closedRef <- newIORef False
    let wsApp pending = do
          conn <- WS.acceptRequest pending
          result <- try $ WS.receiveDataMessage conn :: IO (Either WS.ConnectionException WS.DataMessage)
          case result of
            Left _ -> writeIORef closedRef True
            Right _ -> return ()
        app = Http.mkApp testHttpHandler (Just ("/ws", wsApp))
    withApp app $ \port -> do
      WS.runClient "127.0.0.1" port "/ws" $ \conn -> do
        WS.sendClose conn ("bye" :: Text)
        threadDelay 100000
      threadDelay 100000
      closed <- readIORef closedRef
      closed `shouldBe` True

  it "disconnect without close frame does not crash server" $ do
    let wsApp pending = do
          conn <- WS.acceptRequest pending
          _ <- try $ WS.receiveDataMessage conn :: IO (Either SomeException WS.DataMessage)
          return ()
        app = Http.mkApp testHttpHandler (Just ("/ws", wsApp))
    withApp app $ \port -> do
      -- Connect via raw socket, send upgrade, then close abruptly
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
        threadDelay 50000
      -- Server should still work
      threadDelay 100000
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

      threadDelay 50000
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
  agentStateRef <- newIORef "0"
  let observe = do
        n <- readIORef stateRef
        return (T.pack (show n))
      step _ = do
        n <- atomicModifyIORef' stateRef (\n' -> (n' + 1, n' + 1))
        let output = T.pack (show n)
        writeIORef agentStateRef output
        return output
  let agent = Agent.AgentDef
        { Agent.agentName = "counter"
        , Agent.agentPath = "/counter"
        , Agent.agentState = agentStateRef
        , Agent.agentObserve = observe
        , Agent.agentStep = step
        }
  app <- Agent.mkAgentApp corsOrigin [agent]
  withApp app action
