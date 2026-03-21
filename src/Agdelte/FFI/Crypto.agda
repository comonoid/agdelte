{-# OPTIONS --without-K #-}

-- Cryptographic primitives via Haskell FFI (MAlonzo only).
-- Backed by cryptonite (HMAC, random) and bcrypt (password hashing).

module Agdelte.FFI.Crypto where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Nat using (Nat)

{-# FOREIGN GHC import qualified Agdelte.Crypto as Crypto #-}

------------------------------------------------------------------------
-- HMAC-SHA256
------------------------------------------------------------------------

-- | HMAC-SHA256: secret × message → hex digest
postulate
  hmacSHA256 : String → String → String

{-# COMPILE GHC hmacSHA256 = Crypto.hmacSHA256 #-}

------------------------------------------------------------------------
-- Password hashing (bcrypt)
------------------------------------------------------------------------

-- | Hash password with bcrypt (cost 12). IO because of random salt.
postulate
  hashPassword : String → IO String

{-# COMPILE GHC hashPassword = Crypto.hashPassword #-}

-- | Verify password against bcrypt hash. Pure (no IO needed).
postulate
  verifyPassword : String → String → Bool

{-# COMPILE GHC verifyPassword = Crypto.verifyPassword #-}

------------------------------------------------------------------------
-- Random bytes
------------------------------------------------------------------------

-- | Generate N random bytes as base64-encoded string.
postulate
  randomBytesB64 : Nat → IO String

{-# COMPILE GHC randomBytesB64 = Crypto.randomBytesB64 #-}

------------------------------------------------------------------------
-- Base64
------------------------------------------------------------------------

-- | Base64 encode
postulate
  base64Encode : String → String

{-# COMPILE GHC base64Encode = Crypto.base64Encode #-}

-- | Base64 decode (returns "" on invalid input)
postulate
  base64Decode : String → String

{-# COMPILE GHC base64Decode = Crypto.base64Decode #-}

------------------------------------------------------------------------
-- Constant-time comparison
------------------------------------------------------------------------

-- | Constant-time string comparison (prevents timing attacks on HMAC).
postulate
  constantTimeEq : String → String → Bool

{-# FOREIGN GHC
  import qualified Data.Text as T
  import qualified Data.Text.Encoding as TE
  import qualified Data.ByteArray as BA

  constantTimeEqHS :: T.Text -> T.Text -> Bool
  constantTimeEqHS a b = BA.constEq (TE.encodeUtf8 a) (TE.encodeUtf8 b)
  #-}
{-# COMPILE GHC constantTimeEq = constantTimeEqHS #-}
