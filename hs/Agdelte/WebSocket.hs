{-# LANGUAGE OverloadedStrings #-}
-- | Minimal WebSocket server on raw sockets
-- No websockets library dependency — manual framing
-- Supports text frames, ping/pong, close
module Agdelte.WebSocket
  ( WsConn
  , wsAccept
  , wsSend
  , wsReceive
  , wsClose
  , WsMessage(..)
  ) where

import Control.Exception (SomeException, try, catch)
import Data.Bits ((.&.), (.|.), xor, shiftL, shiftR)
import Data.Word (Word8, Word16, Word64)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BS8
import qualified Data.ByteString.Base64 as B64
import qualified Crypto.Hash as H
import qualified Data.ByteArray as BA
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Network.Socket (Socket)
import Network.Socket.ByteString (recv, sendAll)

-- | WebSocket connection (wrapper around raw socket)
newtype WsConn = WsConn Socket

-- | WebSocket message types
data WsMessage
  = WsText Text
  | WsPing BS.ByteString
  | WsPong BS.ByteString
  | WsClose
  deriving (Show)

-- | WebSocket magic GUID
wsMagic :: BS.ByteString
wsMagic = BS8.pack "258EAFA5-E914-47DA-95CA-C5AB0DC85B11"

-- | Compute Sec-WebSocket-Accept from client key
computeAccept :: BS.ByteString -> BS.ByteString
computeAccept clientKey =
  let combined = BS.filter (/= 0x0d) (BS.filter (/= 0x0a) (BS.filter (/= 0x20) clientKey)) <> wsMagic
      digest = H.hash combined :: H.Digest H.SHA1
  in B64.encode (BS.pack (BA.unpack digest))

-- | Perform WebSocket handshake on existing socket with raw HTTP request data
-- Returns WsConn if upgrade succeeds, Nothing otherwise
wsAccept :: Socket -> BS.ByteString -> IO (Maybe WsConn)
wsAccept sock rawRequest = do
  let headers = parseHeaders rawRequest
  case lookup "Sec-WebSocket-Key" headers of
    Nothing -> return Nothing
    Just key -> do
      let accept = computeAccept (BS8.pack (T.unpack key))
      let response = BS8.unlines
            [ "HTTP/1.1 101 Switching Protocols"
            , "Upgrade: websocket"
            , "Connection: Upgrade"
            , BS8.pack "Sec-WebSocket-Accept: " <> accept
            , ""
            , ""
            ]
      sendAll sock response
      return (Just (WsConn sock))

-- | Parse HTTP headers from raw request
parseHeaders :: BS.ByteString -> [(Text, Text)]
parseHeaders raw =
  let ls = BS8.lines raw
      parseHeader l =
        case BS8.break (== ':') l of
          (k, v) | not (BS.null v) ->
            Just (TE.decodeUtf8 (BS.filter (/= 0x0d) k),
                  T.strip (TE.decodeUtf8 (BS.filter (/= 0x0d) (BS.drop 1 v))))
          _ -> Nothing
  in [ (k, v) | l <- drop 1 ls, Just (k, v) <- [parseHeader l] ]

-- | Send text frame
wsSend :: WsConn -> Text -> IO ()
wsSend (WsConn sock) msg = do
  let payload = TE.encodeUtf8 msg
      frame = encodeFrame 0x81 payload  -- 0x81 = FIN + text opcode
  sendAll sock frame

-- | Encode a WebSocket frame (server->client, no masking)
encodeFrame :: Word8 -> BS.ByteString -> BS.ByteString
encodeFrame opcode payload =
  let len = BS.length payload
      header
        | len < 126     = BS.pack [opcode, fromIntegral len]
        | len < 65536   = BS.pack [opcode, 126,
                            fromIntegral (len `shiftR` 8),
                            fromIntegral (len .&. 0xFF)]
        | otherwise     = BS.pack [opcode, 127] <> encodeWord64BE (fromIntegral len)
  in header <> payload

encodeWord64BE :: Word64 -> BS.ByteString
encodeWord64BE w = BS.pack
  [ fromIntegral (w `shiftR` 56), fromIntegral (w `shiftR` 48)
  , fromIntegral (w `shiftR` 40), fromIntegral (w `shiftR` 32)
  , fromIntegral (w `shiftR` 24), fromIntegral (w `shiftR` 16)
  , fromIntegral (w `shiftR` 8),  fromIntegral w ]

-- | Receive next WebSocket message
wsReceive :: WsConn -> IO (Maybe WsMessage)
wsReceive (WsConn sock) = do
  result <- try $ do
    hdr <- recvExact sock 2
    if BS.null hdr then return Nothing
    else do
      let byte0 = BS.index hdr 0
          byte1 = BS.index hdr 1
          opcode = byte0 .&. 0x0F
          masked = byte1 .&. 0x80 /= 0
          lenByte = byte1 .&. 0x7F

      payloadLen <- getPayloadLength sock lenByte

      maskKey <- if masked
        then recvExact sock 4
        else return BS.empty

      payload <- recvExact sock (fromIntegral payloadLen)

      let unmasked = if masked then unmask maskKey payload else payload

      case opcode of
        0x1 -> return (Just (WsText (TE.decodeUtf8 unmasked)))  -- text
        0x8 -> return (Just WsClose)                              -- close
        0x9 -> do                                                  -- ping -> pong
          sendAll sock (encodeFrame 0x8A unmasked)
          return (Just (WsPing unmasked))
        0xA -> return (Just (WsPong unmasked))                    -- pong
        _   -> return Nothing                                      -- unknown

  case result of
    Left (_ :: SomeException) -> return Nothing
    Right msg -> return msg

getPayloadLength :: Socket -> Word8 -> IO Word64
getPayloadLength sock lenByte
  | lenByte < 126  = return (fromIntegral lenByte)
  | lenByte == 126 = do
      bs <- recvExact sock 2
      return $ fromIntegral (BS.index bs 0) `shiftL` 8
           .|. fromIntegral (BS.index bs 1)
  | otherwise      = do
      bs <- recvExact sock 8
      return $ foldl (\acc i -> acc `shiftL` 8 .|. fromIntegral (BS.index bs i)) 0 [0..7]

-- | Unmask payload
unmask :: BS.ByteString -> BS.ByteString -> BS.ByteString
unmask key payload = BS.pack $ zipWith xor (BS.unpack payload) (cycle (BS.unpack key))

-- | Receive exactly n bytes
recvExact :: Socket -> Int -> IO BS.ByteString
recvExact _ 0 = return BS.empty
recvExact sock n = go BS.empty n
  where
    go acc 0 = return acc
    go acc remaining = do
      chunk <- recv sock (min remaining 65536)
      if BS.null chunk
        then return acc
        else go (acc <> chunk) (remaining - BS.length chunk)

-- | Send close frame
wsClose :: WsConn -> IO ()
wsClose (WsConn sock) =
  sendAll sock (encodeFrame 0x88 BS.empty) `catch` \(_ :: SomeException) -> return ()
