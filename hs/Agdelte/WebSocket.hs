{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Agdelte.WebSocket
  ( WsConn
  , mkWsConn
  , unwrapConn
  , wsSend
  , wsReceive
  , wsClose
  , WsMessage(..)
  ) where

import Control.Exception (SomeAsyncException(..), SomeException, catch, fromException, throwIO)
import Data.Text (Text)
import System.IO (hPutStrLn, stderr)
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.Encoding as TLE
import Data.Text.Encoding.Error (lenientDecode)
import qualified Network.WebSockets as WS

-- | WebSocket connection (wrapper around websockets library Connection)
newtype WsConn = WsConn WS.Connection

-- | Construct a WsConn from a raw Connection
mkWsConn :: WS.Connection -> WsConn
mkWsConn = WsConn

-- | Unwrap to raw Connection (for ping thread, etc.)
unwrapConn :: WsConn -> WS.Connection
unwrapConn (WsConn c) = c

-- | WebSocket message types
data WsMessage
  = WsText Text
  | WsClose
  deriving (Show)

-- | Send text frame
wsSend :: WsConn -> Text -> IO ()
wsSend (WsConn conn) msg = WS.sendTextData conn msg

-- | Receive next WebSocket message.
-- Returns WsClose on close frame, connection error, or connection closed.
-- Binary frames are silently skipped (up to 100 consecutive binary frames
-- to prevent infinite recursion if the peer only sends binary data).
-- Catches all exceptions (connection errors, IO errors, etc.) and returns WsClose.
wsReceive :: WsConn -> IO WsMessage
wsReceive conn = wsReceive' conn (100 :: Int)

wsReceive' :: WsConn -> Int -> IO WsMessage
wsReceive' (WsConn conn) remaining
  | remaining <= 0 = do
      hPutStrLn stderr "wsReceive: 100 consecutive binary frames, treating as disconnect"
      return WsClose
  | otherwise =
      (do dm <- WS.receiveDataMessage conn
          case dm of
            WS.Text _ (Just txt) ->
              return (WsText (TL.toStrict txt))
            WS.Text bs Nothing ->
              return (WsText (TL.toStrict (TLE.decodeUtf8With lenientDecode bs)))
            _ -> wsReceive' (WsConn conn) (remaining - 1))  -- Binary etc. — skip
      `catch` \(e :: SomeException) ->
        case fromException e of
          Just (SomeAsyncException _) -> throwIO e  -- re-raise async (killThread, cancel)
          Nothing ->
            -- CloseRequest, ConnectionClosed, ParseException, UnicodeException,
            -- IOError from underlying socket, etc.
            return WsClose

-- | Send close frame (safe to call on already-closed connections).
-- Swallows ALL exceptions including async — this is intentional:
-- wsClose is used as cleanup inside bracket_, where throwing would
-- replace the original exception (see GHC bracket/onException semantics).
wsClose :: WsConn -> IO ()
wsClose (WsConn conn) =
  WS.sendClose conn ("bye" :: Text) `catch` \(_ :: SomeException) -> return ()
