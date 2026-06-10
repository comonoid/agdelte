{-# OPTIONS --without-K #-}

-- Minimal JWT (HS256) implementation.
-- Signs and verifies tokens using HMAC-SHA256 from FFI.Crypto.
-- Token format: base64(header).base64(payload).signature
-- Payload is opaque JSON string — caller handles claims.

module Agdelte.Auth.JWT where

open import Agda.Builtin.String using (String)
open import Data.String using (_++_; _≟_)
open import Data.Bool using (if_then_else_)
open import Data.Nat using (ℕ; _≤ᵇ_)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapMaybe)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)

open import Agdelte.FFI.Crypto using (hmacSHA256; base64Encode; base64Decode; constantTimeEq)
open import Agdelte.FFI.Json using (jsonGetNat)

------------------------------------------------------------------------
-- Split JWT into parts (header.payload.signature)
------------------------------------------------------------------------

-- FFI boundary triple, bound to a Haskell nested 2-tuple. Agda's Σ/_×_ can't
-- cross a COMPILE GHC type, so splitJWT returns this opaque type and a pure
-- wrapper rebuilds the (String × String × String) public result.
postulate
  JwtParts : Set
  jpH : JwtParts → String
  jpP : JwtParts → String
  jpS : JwtParts → String
{-# FOREIGN GHC
  import qualified Data.Text as T
  type JwtPartsH = (T.Text, (T.Text, T.Text))
  #-}
{-# COMPILE GHC JwtParts = type JwtPartsH #-}
{-# COMPILE GHC jpH = (\ x -> case x of (h,_)     -> h :: T.Text) #-}
{-# COMPILE GHC jpP = (\ x -> case x of (_,(p,_)) -> p :: T.Text) #-}
{-# COMPILE GHC jpS = (\ x -> case x of (_,(_,s)) -> s :: T.Text) #-}

postulate
  splitJWTRaw : String → Maybe JwtParts

{-# FOREIGN GHC
  splitJWTImpl :: T.Text -> Maybe (T.Text, (T.Text, T.Text))
  splitJWTImpl token =
    case T.splitOn "." token of
      [h, p, s] -> Just (h, (p, s))
      _         -> Nothing
  #-}

{-# COMPILE GHC splitJWTRaw = splitJWTImpl #-}

splitJWT : String → Maybe (String × String × String)
splitJWT s = mapMaybe (λ x → jpH x , jpP x , jpS x) (splitJWTRaw s)

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

-- | Verify JWT signature AND expiry. Returns decoded payload if valid.
-- Uses constant-time comparison to prevent timing attacks.
-- `now` is the current unix timestamp (seconds). A token is rejected if its
-- signature is invalid, if it has no `exp` claim, or if it has expired
-- (now ≥ exp). Tokens without `exp` are rejected on purpose: every token
-- issued by mkToken carries one, so a missing `exp` means a malformed or
-- legacy token that must not be trusted indefinitely.
verifyJWT : String → ℕ → String → Maybe String
verifyJWT secret now token with splitJWT token
... | nothing = nothing
... | just (header , payload , sig) =
  if constantTimeEq (hmacSHA256 secret (header ++ "." ++ payload)) sig
  then checkExp (base64Decode payload)
  else nothing
  where
    checkExp : String → Maybe String
    checkExp decoded with jsonGetNat "exp" decoded
    ... | nothing  = nothing                          -- no exp claim → reject
    ... | just exp = if exp ≤ᵇ now then nothing        -- expired
                     else just decoded
