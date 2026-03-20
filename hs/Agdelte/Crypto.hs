{-# LANGUAGE OverloadedStrings #-}
module Agdelte.Crypto
  ( hmacSHA256
  , hashPassword
  , verifyPassword
  , randomBytesB64
  , base64Encode
  , base64Decode
  ) where

import qualified Crypto.Hash as Hash
import qualified Crypto.MAC.HMAC as HMAC
import qualified Crypto.KDF.BCrypt as BCrypt
import qualified Data.ByteArray as BA
import qualified Data.ByteString as BS
import qualified Data.ByteString.Base64 as B64
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Crypto.Random (getRandomBytes)

-- | HMAC-SHA256: secret (text) × message (text) → hex digest (text)
hmacSHA256 :: T.Text -> T.Text -> T.Text
hmacSHA256 secret msg =
  let key = TE.encodeUtf8 secret
      dat = TE.encodeUtf8 msg
      digest = HMAC.hmac key dat :: HMAC.HMAC Hash.SHA256
  in T.pack (show digest)

-- | Hash password with bcrypt (cost 12). Returns base64-encoded hash.
hashPassword :: T.Text -> IO T.Text
hashPassword pwd = do
  let pwdBS = TE.encodeUtf8 pwd
  hash <- BCrypt.hashPassword 12 pwdBS
  return (TE.decodeUtf8 hash)

-- | Verify password against bcrypt hash. Returns True/False.
verifyPassword :: T.Text -> T.Text -> Bool
verifyPassword pwd hash =
  BCrypt.validatePassword (TE.encodeUtf8 pwd) (TE.encodeUtf8 hash)

-- | Generate N random bytes, return as base64 text.
randomBytesB64 :: Integer -> IO T.Text
randomBytesB64 n = do
  bytes <- getRandomBytes (fromIntegral n) :: IO BS.ByteString
  return (TE.decodeUtf8 (B64.encode bytes))

-- | Base64 encode text → text
base64Encode :: T.Text -> T.Text
base64Encode = TE.decodeUtf8 . B64.encode . TE.encodeUtf8

-- | Base64 decode text → text (returns empty on invalid input)
base64Decode :: T.Text -> T.Text
base64Decode t = case B64.decode (TE.encodeUtf8 t) of
  Right bs -> TE.decodeUtf8 bs
  Left _   -> ""
