{-# OPTIONS --without-K --guardedness #-}

-- Auth middleware for Agdelte HTTP server.
-- Extracts and validates JWT from Authorization header.
-- Provides withAuth combinator for protected endpoints.

module Agdelte.Auth.Middleware where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.String using (_++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)

open import Agdelte.FFI.Server using
  ( HttpRequest; HttpResponse; reqHeaders; reqMethod; reqPath; reqBody
  ; mkResponse; mkResponseH; lookupHeader
  ; _>>=_; pure
  )
open import Agdelte.Auth.JWT using (verifyJWT)

------------------------------------------------------------------------
-- Auth types
------------------------------------------------------------------------

-- | Authenticated request: carries decoded JWT payload alongside raw request.
record AuthRequest : Set where
  constructor mkAuthRequest
  field
    authPayload : String        -- decoded JWT payload (JSON)
    authRaw     : HttpRequest   -- original request

open AuthRequest public

------------------------------------------------------------------------
-- Token extraction
------------------------------------------------------------------------

-- | Extract Bearer token from Authorization header.
-- "Bearer eyJ..." → just "eyJ..."
-- anything else → nothing
postulate
  extractBearer : String → Maybe String

{-# FOREIGN GHC
  import qualified Data.Text as T

  extractBearerImpl :: T.Text -> Maybe T.Text
  extractBearerImpl h =
    case T.stripPrefix "Bearer " h of
      Just token -> Just (T.strip token)
      Nothing    -> Nothing
  #-}
{-# COMPILE GHC extractBearer = extractBearerImpl #-}

------------------------------------------------------------------------
-- Auth middleware
------------------------------------------------------------------------

-- | Authenticate request: extract JWT from Authorization header, verify, return payload.
authenticate : String → HttpRequest → Maybe String
authenticate secret req =
  case lookupHeader "Authorization" (reqHeaders req) of λ where
    nothing → nothing
    (just authHeader) →
      case extractBearer authHeader of λ where
        nothing → nothing
        (just token) → verifyJWT secret token
  where
    case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
    case x of f = f x

-- | Wrap a handler to require authentication.
-- Returns 401 if no valid token, otherwise passes AuthRequest to handler.
withAuth : String → (AuthRequest → IO HttpResponse) → HttpRequest → IO HttpResponse
withAuth secret handler req with authenticate secret req
... | nothing      = pure (mkResponse 401 "{\"error\":\"Unauthorized\"}")
... | just payload = handler (mkAuthRequest payload req)

------------------------------------------------------------------------
-- CORS headers
-- WARNING: Origin "*" is for development only.
-- In production, restrict to the actual frontend domain.
------------------------------------------------------------------------

corsHeaders : List (String × String)
corsHeaders =
    ("Access-Control-Allow-Origin" , "*")
  ∷ ("Access-Control-Allow-Headers" , "Authorization, Content-Type")
  ∷ ("Access-Control-Allow-Methods" , "GET, POST, OPTIONS")
  ∷ []

-- | Handle OPTIONS preflight with CORS headers.
handleOptions : IO HttpResponse
handleOptions = pure (mkResponseH 204 "" corsHeaders)
