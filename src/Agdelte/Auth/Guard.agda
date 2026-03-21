{-# OPTIONS --without-K --guardedness #-}

-- Authorization guards: role-based, purchase-based, ownership-based.
-- Built on top of withAuth from Middleware.

module Agdelte.Auth.Guard where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Bool using (if_then_else_)
open import Data.String using (_++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.List using (List)
open import Data.Product using (_×_; _,_)

open import Agdelte.FFI.Server using
  ( HttpRequest; HttpResponse
  ; mkResponse; mkResponseH
  ; _>>=_; pure
  )
open import Agdelte.Auth.Middleware using
  ( AuthRequest; mkAuthRequest; authPayload; authRaw
  ; authenticate; corsHeaders
  )
open import Agdelte.FFI.Json using (escapeJsonString; jsonGetField; jsonGetNat)
open import Agdelte.Auth.Role using (Role; roleAtLeast; parseRole)
open import Agdelte.Storage.WAL using (WalHandle; walRead)
open import Agdelte.Storage.AppStore
open import Agdelte.FFI.Time using (getCurrentTime)
open import Agdelte.Util using (case_of_)

------------------------------------------------------------------------
-- Payload helpers
------------------------------------------------------------------------

-- | Extract user ID from JWT payload
extractSub : String → Maybe ℕ
extractSub = jsonGetNat "sub"

-- | Extract role from JWT payload
extractRole : String → Maybe Role
extractRole payload with jsonGetField "role" payload
... | nothing = nothing
... | just s  = parseRole s

------------------------------------------------------------------------
-- Response helpers
------------------------------------------------------------------------

private
  resp401 : HttpResponse
  resp401 = mkResponseH 401 "{\"error\":\"Unauthorized\"}" corsHeaders

  resp403 : HttpResponse
  resp403 = mkResponseH 403 "{\"error\":\"Forbidden\"}" corsHeaders

  resp403Msg : String → HttpResponse
  resp403Msg msg = mkResponseH 403 ("{\"error\":\"" ++ escapeJsonString msg ++ "\"}") corsHeaders

------------------------------------------------------------------------
-- Guards
------------------------------------------------------------------------

-- | Require authentication + minimum role.
-- Checks JWT validity, extracts role from payload, compares with required.
withRole : String → Role → (AuthRequest → IO HttpResponse) → HttpRequest → IO HttpResponse
withRole secret requiredRole handler req with authenticate secret req
... | nothing      = pure resp401
... | just payload with extractRole payload
...   | nothing   = pure resp401
...   | just role with roleAtLeast requiredRole role
...     | false = pure resp403
...     | true  = handler (mkAuthRequest payload req)

-- | Require authentication + course access (subscription OR individual purchase).
-- Extracts userId from JWT, checks active subscription or paid purchase.
-- Gets current time internally via IO.
withAccess : String → WalHandle AppState AppOp → CourseId
           → (AuthRequest → IO HttpResponse) → HttpRequest → IO HttpResponse
withAccess secret wal courseId handler req with authenticate secret req
... | nothing      = pure resp401
... | just payload with extractSub payload
...   | nothing  = pure resp401
...   | just uid =
        getCurrentTime >>= λ now →
        walRead wal >>= λ state →
        if userCanAccess uid courseId now state
        then handler (mkAuthRequest payload req)
        else pure (resp403Msg "Subscription or purchase required")

-- | Backwards-compatible alias (without time check — no subscription support).
-- Prefer withAccess for new code.
withPurchase : String → WalHandle AppState AppOp → CourseId
             → (AuthRequest → IO HttpResponse) → HttpRequest → IO HttpResponse
withPurchase secret wal courseId handler req with authenticate secret req
... | nothing      = pure resp401
... | just payload with extractSub payload
...   | nothing  = pure resp401
...   | just uid =
        walRead wal >>= λ state →
        if userHasCourse uid courseId state
        then handler (mkAuthRequest payload req)
        else pure (resp403Msg "Course not purchased")

-- | Require authentication + course ownership (author).
-- For instructor-only endpoints that modify their own courses.
withOwner : String → WalHandle AppState AppOp → CourseId
          → (AuthRequest → IO HttpResponse) → HttpRequest → IO HttpResponse
withOwner secret wal courseId handler req with authenticate secret req
... | nothing      = pure resp401
... | just payload with extractSub payload
...   | nothing  = pure resp401
...   | just uid =
        walRead wal >>= λ state →
        case findCourseById courseId state of λ where
          nothing → pure (mkResponseH 404 "{\"error\":\"Course not found\"}" corsHeaders)
          (just course) →
            if crAuthorId course ≡ᵇ uid
            then handler (mkAuthRequest payload req)
            else -- Admin can also edit any course
              case extractRole payload of λ where
                (just role) → if roleAtLeast Admin role
                  then handler (mkAuthRequest payload req)
                  else pure (resp403Msg "Not course owner")
                nothing → pure (resp403Msg "Not course owner")
        where
          open Data.Nat using (_≡ᵇ_)
          open import Agdelte.Auth.Role using (Admin)
