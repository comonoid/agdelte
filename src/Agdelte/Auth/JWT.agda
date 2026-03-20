{-# OPTIONS --without-K #-}

-- Minimal JWT (HS256) implementation.
-- Signs and verifies tokens using HMAC-SHA256 from FFI.Crypto.
-- Token format: base64(header).base64(payload).signature
-- Payload is opaque JSON string — caller handles claims.

module Agdelte.Auth.JWT where

open import Agda.Builtin.String using (String)
open import Data.String using (_++_; _≟_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)

open import Agdelte.FFI.Crypto using (hmacSHA256; base64Encode; base64Decode)

------------------------------------------------------------------------
-- Split JWT into parts (header.payload.signature)
------------------------------------------------------------------------

postulate
  splitJWT : String → Maybe (String × String × String)

{-# FOREIGN GHC
  import qualified Data.Text as T

  splitJWTImpl :: T.Text -> Maybe (T.Text, (T.Text, T.Text))
  splitJWTImpl token =
    case T.splitOn "." token of
      [h, p, s] -> Just (h, (p, s))
      _         -> Nothing
  #-}
{-# COMPILE GHC splitJWT = splitJWTImpl #-}

------------------------------------------------------------------------
-- JWT header (fixed: HS256 + JWT)
------------------------------------------------------------------------

private
  jwtHeader : String
  jwtHeader = base64Encode "{\"alg\":\"HS256\",\"typ\":\"JWT\"}"

------------------------------------------------------------------------
-- Sign: create JWT from payload string
------------------------------------------------------------------------

-- | Create a signed JWT. Payload should be a JSON string.
signJWT : String → String → String
signJWT secret payload =
  let encodedPayload = base64Encode payload
      signingInput   = jwtHeader ++ "." ++ encodedPayload
      signature      = hmacSHA256 secret signingInput
  in signingInput ++ "." ++ signature

------------------------------------------------------------------------
-- Verify: check signature and extract payload
------------------------------------------------------------------------

-- | Verify JWT signature. Returns decoded payload if valid, nothing if invalid.
verifyJWT : String → String → Maybe String
verifyJWT secret token with splitJWT token
... | nothing = nothing
... | just (header , payload , sig) with hmacSHA256 secret (header ++ "." ++ payload) ≟ sig
...   | yes _ = just (base64Decode payload)
...   | no _  = nothing
