{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Agdelte.WebSocket
  ( WsConn(..)
  , wsSend
  , wsReceive
  , wsClose
  , WsMessage(..)
  ) where

import Control.Exception (SomeException, catch)
import Data.Text (Text)
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.Encoding as TLE
import qualified Network.WebSockets as WS

-- | WebSocket connection (wrapper around websockets library Connection)
newtype WsConn = WsConn WS.Connection

-- | WebSocket message types
data WsMessage
  = WsText Text
  | WsClose
  deriving (Show)

-- | Send text frame
wsSend :: WsConn -> Text -> IO ()
wsSend (WsConn conn) msg = WS.sendTextData conn msg

-- | Receive next WebSocket message.
-- Returns Just WsClose on close frame, connection error, or connection closed.
-- Binary frames are silently skipped (up to 100 consecutive binary frames
-- to prevent infinite recursion if the peer only sends binary data).
-- Catches only WS.ConnectionException — async exceptions propagate.
wsReceive :: WsConn -> IO (Maybe WsMessage)
wsReceive conn = wsReceive' conn (100 :: Int)

wsReceive' :: WsConn -> Int -> IO (Maybe WsMessage)
wsReceive' (WsConn conn) remaining
  | remaining <= 0 = return (Just WsClose)  -- too many binary frames, treat as close
  | otherwise =
      (do dm <- WS.receiveDataMessage conn
          case dm of
            WS.Text _ (Just txt) ->
              return (Just (WsText (TL.toStrict txt)))
            WS.Text bs Nothing ->
              return (Just (WsText (TL.toStrict (TLE.decodeUtf8 bs))))
            _ -> wsReceive' (WsConn conn) (remaining - 1))  -- Binary etc. — skip
      `catch` \(_ :: WS.ConnectionException) ->
        -- CloseRequest, ConnectionClosed, ParseException, UnicodeException
        return (Just WsClose)

-- | Send close frame (safe to call on already-closed connections)
wsClose :: WsConn -> IO ()
wsClose (WsConn conn) =
  WS.sendClose conn ("bye" :: Text) `catch` \(_ :: SomeException) -> return ()
