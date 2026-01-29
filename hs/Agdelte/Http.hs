-- | Minimal HTTP + WebSocket server using Network.Socket
-- No warp/websockets dependency — raw sockets
module Agdelte.Http
  ( serve
  , serveWithWs
  , Request(..)
  , Response(..)
  ) where

import Control.Concurrent (forkIO)
import Control.Exception (bracket, SomeException, try)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BS8
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Network.Socket
import Network.Socket.ByteString (recv, sendAll)

import qualified Agdelte.WebSocket as WS

data Request = Request
  { reqMethod :: Text
  , reqPath   :: Text
  , reqBody   :: Text
  } deriving (Show)

data Response = Response
  { resStatus :: Int
  , resBody   :: Text
  }

-- | Start HTTP server on given port, call handler for each request
serve :: Int -> (Request -> IO Response) -> IO ()
serve port handler = serveWithWs port handler Nothing

-- | Start HTTP + WebSocket server
-- When wsHandler is Just, WebSocket upgrade requests on matching path are handled
serveWithWs :: Int
            -> (Request -> IO Response)                    -- HTTP handler
            -> Maybe (Text, WS.WsConn -> IO ())           -- (path, WS handler)
            -> IO ()
serveWithWs port httpHandler wsHandler = do
  let hints = defaultHints { addrFlags = [AI_PASSIVE], addrSocketType = Stream }
  addr:_ <- getAddrInfo (Just hints) Nothing (Just (show port))
  bracket (openSocket addr) close $ \sock -> do
    setSocketOption sock ReuseAddr 1
    bind sock (addrAddress addr)
    listen sock 128
    putStrLn $ "Agdelte server listening on port " ++ show port
    acceptLoop sock httpHandler wsHandler

acceptLoop :: Socket -> (Request -> IO Response) -> Maybe (Text, WS.WsConn -> IO ()) -> IO ()
acceptLoop sock httpHandler wsHandler = do
  (conn, _) <- accept sock
  _ <- forkIO $ handleConnection conn httpHandler wsHandler
  acceptLoop sock httpHandler wsHandler

handleConnection :: Socket -> (Request -> IO Response) -> Maybe (Text, WS.WsConn -> IO ()) -> IO ()
handleConnection conn httpHandler wsHandler = do
  result <- try $ do
    raw <- recv conn 65536
    if BS.null raw
      then return ()
      else do
        let req = parseRequest raw
        -- Check for WebSocket upgrade
        case wsHandler of
          Just (wsPath, handler) | isWsUpgrade raw && reqPath req == wsPath -> do
            mConn <- WS.wsAccept conn raw
            case mConn of
              Just wsConn -> handler wsConn  -- This blocks until WS handler exits
              Nothing -> do
                let resp = Response 400 (T.pack "Bad WebSocket handshake")
                sendAll conn (formatResponse resp)
          _ -> do
            resp <- httpHandler req
            sendAll conn (formatResponse resp)
  case result of
    Left (_ :: SomeException) -> return ()
    Right _ -> return ()
  close conn

-- | Check if request is a WebSocket upgrade
isWsUpgrade :: BS.ByteString -> Bool
isWsUpgrade raw =
  BS8.isInfixOf (BS8.pack "Upgrade: websocket") raw ||
  BS8.isInfixOf (BS8.pack "upgrade: websocket") raw

parseRequest :: BS.ByteString -> Request
parseRequest raw =
  let ls = BS8.lines raw
      (method, rest) = case ls of
        (l:_) -> let ws = BS8.words l
                 in case ws of
                      (m:p:_) -> (TE.decodeUtf8 m, TE.decodeUtf8 p)
                      _       -> (T.pack "GET", T.pack "/")
        []    -> (T.pack "GET", T.pack "/")
      -- Body is after empty line
      body = case break BS.null ls of
               (_, _:bodyLines) -> TE.decodeUtf8 (BS8.unlines bodyLines)
               _                -> T.empty
  in Request method rest body

formatResponse :: Response -> BS.ByteString
formatResponse (Response status body) =
  let bodyBS = TE.encodeUtf8 body
      statusText = case status of
        200 -> "OK"
        400 -> "Bad Request"
        404 -> "Not Found"
        405 -> "Method Not Allowed"
        _   -> "Unknown"
      header = BS8.intercalate (BS8.pack "\r\n")
        [ BS8.pack $ "HTTP/1.1 " ++ show status ++ " " ++ statusText
        , BS8.pack "Content-Type: application/json"
        , BS8.pack $ "Content-Length: " ++ show (BS.length bodyBS)
        , BS8.pack "Access-Control-Allow-Origin: *"
        , BS8.pack "Access-Control-Allow-Methods: GET, POST, OPTIONS"
        , BS8.pack "Access-Control-Allow-Headers: Content-Type"
        , BS8.pack "Connection: close"
        , BS8.pack ""
        , BS8.pack ""
        ]
  in header <> bodyBS
