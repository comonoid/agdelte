{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Agdelte.Http
  ( serve, serveWithWs, mkApp, toWaiApp, Request(..), Response(..)
  ) where

import Control.Exception (SomeAsyncException(..), SomeException, fromException, throwIO, try)
import Data.Text (Text)
import qualified Data.Text.Encoding as TE
import Data.Text.Encoding.Error (lenientDecode)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as LBS
import qualified Data.CaseInsensitive as CI
import System.IO (hPutStrLn, stderr)
import qualified Network.Wai as Wai
import qualified Network.Wai.Handler.Warp as Warp
import qualified Network.HTTP.Types as H
import qualified Network.WebSockets as WS
import qualified Network.Wai.Handler.WebSockets as WaiWS

-- Types preserved for FFI compatibility with Server.agda
data Request = Request
  { reqMethod  :: Text
  , reqPath    :: Text
  , reqBody    :: Text
  , reqHeaders :: [(Text, Text)]
  }
  deriving (Show)

data Response = Response
  { resStatus  :: Int
  , resBody    :: Text
  , resHeaders :: [(Text, Text)]
  }

serve :: Int -> (Request -> IO Response) -> IO ()
serve port handler = do
  putStrLn $ "Agdelte server listening on port " ++ show port
  serveWithWs port handler Nothing

serveWithWs :: Int -> (Request -> IO Response) -> Maybe (Text, WS.ServerApp) -> IO ()
serveWithWs port httpHandler mWsHandler = do
  let settings = Warp.setPort port
               $ Warp.setHost "*"
               $ Warp.defaultSettings
  Warp.runSettings settings (mkApp httpHandler mWsHandler)

-- | Build WAI Application with optional WebSocket routing (without starting warp).
-- Needed for tests (Warp.testWithApplication).
mkApp :: (Request -> IO Response) -> Maybe (Text, WS.ServerApp) -> Wai.Application
mkApp httpHandler mWsHandler =
  let httpApp = toWaiApp httpHandler
  in case mWsHandler of
    Nothing -> httpApp
    Just (wsPath, wsApp) ->
      let filteredWsApp pending =
            let rqPath = WS.requestPath (WS.pendingRequest pending)
                pathOnly = BS.takeWhile (/= 0x3F) rqPath  -- 0x3F = '?'
            in  if pathOnly == TE.encodeUtf8 wsPath
                then wsApp pending
                else WS.rejectRequest pending "Wrong path"
      in WaiWS.websocketsOr WS.defaultConnectionOptions filteredWsApp httpApp

-- | Maximum request body size (16 MB). Requests with bodies larger than this
-- are rejected with 413 before the full body is read into memory.
maxBodySize :: Int
maxBodySize = 16 * 1024 * 1024

-- | Read request body with size limit. Reads chunks incrementally;
-- returns Left if the limit is exceeded (without reading the rest).
readBodyLimited :: Wai.Request -> Int -> IO (Either () BS.ByteString)
readBodyLimited req limit = go [] 0
  where
    go chunks total = do
      chunk <- Wai.getRequestBodyChunk req
      if BS.null chunk
        then return (Right (BS.concat (reverse chunks)))
        else let total' = total + BS.length chunk
             in if total' > limit
                then return (Left ())
                else go (chunk : chunks) total'

toWaiApp :: (Request -> IO Response) -> Wai.Application
toWaiApp handler waiReq respond = do
  bodyResult <- readBodyLimited waiReq maxBodySize
  case bodyResult of
    Left () -> respond $ Wai.responseLBS H.status413
      [("Content-Type", "text/plain")] "Payload too large"
    Right reqBodyBS -> do
      let hdrs = map (\(k,v) -> ( TE.decodeUtf8With lenientDecode (CI.original k)
                                  , TE.decodeUtf8With lenientDecode v ))
                      (Wai.requestHeaders waiReq)
          req = Request
            { reqMethod  = TE.decodeUtf8With lenientDecode (Wai.requestMethod waiReq)
            , reqPath    = TE.decodeUtf8With lenientDecode (Wai.rawPathInfo waiReq)
            , reqBody    = TE.decodeUtf8With lenientDecode reqBodyBS
            , reqHeaders = hdrs
            }
      handlerResult <- try $ handler req
      case handlerResult of
        Left (e :: SomeException)
          | Just (SomeAsyncException _) <- fromException e -> throwIO e
          | otherwise -> do
          hPutStrLn stderr $ "Http: handler exception: " ++ show e
          respond $ Wai.responseLBS H.status500
            [("Content-Type", "text/plain")] "Internal server error"
        Right resp -> do
          -- Evaluate response body and headers inside try to catch thunked exceptions
          -- (e.g. handler returned Response with resBody = error "boom")
          evalResult <- try $ do
            let !status' = toStatus (resStatus resp)
                !body' = TE.encodeUtf8 (resBody resp)
            -- Force each header element deeply (not just spine) to catch thunked exceptions
            hdrs' <- mapM (\(k,v) -> let !k' = CI.mk (TE.encodeUtf8 k)
                                         !v' = TE.encodeUtf8 v
                                     in return (k', v')) (resHeaders resp)
            return (status', body', hdrs')
          case evalResult of
            Left (e2 :: SomeException)
              | Just (SomeAsyncException _) <- fromException e2 -> throwIO e2
              | otherwise -> do
              hPutStrLn stderr $ "Http: response evaluation failed: " ++ show e2
              respond $ Wai.responseLBS H.status500
                [("Content-Type", "text/plain")] "Internal server error"
            Right (status, respBodyStrict, userHdrs) -> do
              let
                  hasContentType = any (\(k,_) -> CI.foldedCase k == "content-type") userHdrs
                  isOptions = Wai.requestMethod waiReq == "OPTIONS"
                  coopCoep = if isOptions then []
                             else [ ("Cross-Origin-Opener-Policy", "same-origin")
                                  , ("Cross-Origin-Embedder-Policy", "require-corp") ]
                  is204 = resStatus resp == 204
                  defaultHdrs = [("Content-Type", "application/json") | not hasContentType && not is204]
                             ++ coopCoep
                  hdrs = userHdrs ++ defaultHdrs
                  respBodyBS = LBS.fromStrict respBodyStrict
              respond $ Wai.responseLBS status hdrs respBodyBS

-- | Convert Int status code to http-types Status
toStatus :: Int -> H.Status
toStatus 200 = H.status200
toStatus 201 = H.status201
toStatus 202 = H.status202
toStatus 204 = H.status204
toStatus 301 = H.status301
toStatus 302 = H.status302
toStatus 304 = H.status304
toStatus 400 = H.status400
toStatus 403 = H.status403
toStatus 404 = H.status404
toStatus 405 = H.status405
toStatus 408 = H.status408
toStatus 413 = H.status413
toStatus 500 = H.status500
toStatus 502 = H.status502
toStatus 503 = H.status503
toStatus 504 = H.status504
toStatus n   = H.mkStatus n ""
