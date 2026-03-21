{-# OPTIONS --without-K #-}

-- Signed URLs: HMAC-based URL signing with TTL.
-- Used to protect video segments — client gets a signed URL that
-- expires after a set time.

module Agdelte.Auth.SignedUrl where

open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Bool using (if_then_else_)
open import Data.String using (_++_; _≟_)
open import Data.Nat using (ℕ; _<ᵇ_)
open import Data.Nat.Show using (show)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)

open import Agdelte.FFI.Crypto using (hmacSHA256; constantTimeEq)
open import Agdelte.Util using (case_of_)

------------------------------------------------------------------------
-- Signing
------------------------------------------------------------------------

-- | Sign a URL with a secret and expiry timestamp.
-- Format: url?expires=TIMESTAMP&sig=HMAC(secret, url|expires)
signUrl : String → String → ℕ → String
signUrl secret url expires =
  let expiresStr = show expires
      message    = url ++ "|" ++ expiresStr
      sig        = hmacSHA256 secret message
  in url ++ "?expires=" ++ expiresStr ++ "&sig=" ++ sig

------------------------------------------------------------------------
-- Verification
------------------------------------------------------------------------

-- | Parse expires and sig from a signed URL query string.
-- Expects: ...?expires=N&sig=HEX
postulate
  parseSignedParams : String → Maybe (String × ℕ × String)
  -- Returns: (base url, expires, signature)

{-# FOREIGN GHC
  import qualified Data.Text as T
  import Text.Read (readMaybe)

  parseSignedParamsImpl :: T.Text -> Maybe (T.Text, (Integer, T.Text))
  parseSignedParamsImpl fullUrl =
    case T.breakOn "?expires=" fullUrl of
      (_, rest) | T.null rest -> Nothing
      (baseUrl, rest) ->
        let afterQ = T.drop 9 rest  -- drop "?expires="
        in case T.breakOn "&sig=" afterQ of
             (_, sigRest) | T.null sigRest -> Nothing
             (expiresText, sigRest) ->
               let sig = T.drop 5 sigRest  -- drop "&sig="
               in case readMaybe (T.unpack expiresText) :: Maybe Integer of
                    Nothing -> Nothing
                    Just n  -> Just (baseUrl, (n, sig))
  #-}

{-# COMPILE GHC parseSignedParams = parseSignedParamsImpl #-}

-- | Verify a signed URL. Checks signature and expiry.
-- currentTime: unix timestamp in seconds.
verifyUrl : String → ℕ → String → Maybe String
verifyUrl secret currentTime signedUrl with parseSignedParams signedUrl
... | nothing = nothing
... | just (baseUrl , expires , sig) =
  if expires <ᵇ currentTime
  then nothing    -- expired
  else let expected = hmacSHA256 secret (baseUrl ++ "|" ++ show expires)
       in if constantTimeEq expected sig then just baseUrl else nothing
