{-# OPTIONS --without-K --guardedness #-}

-- Auth request handlers: register, login.
-- Uses WAL-backed AppStore for persistence.

module Agdelte.Auth.Handler where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.String using (_++_; _≟_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Nat using (ℕ)
open import Data.Nat.Show using (show)
open import Relation.Nullary using (yes; no)

open import Agdelte.FFI.Server using
  ( HttpRequest; HttpResponse
  ; reqBody; mkResponse; mkResponseH
  ; _>>=_; _>>_; pure
  )
open import Agdelte.FFI.Crypto using (hashPassword; verifyPassword)
open import Agdelte.Auth.JWT using (signJWT)
open import Agdelte.Auth.Middleware using (corsHeaders)
open import Agdelte.Auth.Role using (Role; Student; showRole)
open import Agdelte.Storage.WAL using (WalHandle; walRead; walStep; walModify)
open import Agdelte.Storage.AppStore

open import Agdelte.FFI.Json using (jsonGetField; escapeJsonString) public
open import Agdelte.Util using (case_of_)

------------------------------------------------------------------------
-- Input validation (GHC backend)
------------------------------------------------------------------------

private
  postulate
    isValidEmail    : String → Bool
    isValidPassword : String → Bool

{-# FOREIGN GHC
  import qualified Data.Text as T

  isValidEmailHS :: T.Text -> Bool
  isValidEmailHS t = T.any (== '@') t && T.length t >= 3

  isValidPasswordHS :: T.Text -> Bool
  isValidPasswordHS t = T.length t >= 8
  #-}
{-# COMPILE GHC isValidEmail    = isValidEmailHS #-}
{-# COMPILE GHC isValidPassword = isValidPasswordHS #-}

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

private
  mkToken : String → ℕ → String → Role → String
  mkToken secret uid email role =
    let esc = escapeJsonString
    in signJWT secret ("{\"sub\":" ++ show uid
         ++ ",\"email\":\"" ++ esc email
         ++ "\",\"role\":\"" ++ showRole role ++ "\"}")

  mkAuthResp : ℕ → String → ℕ → HttpResponse
  mkAuthResp status token uid =
    let esc = escapeJsonString
    in mkResponseH status
         ("{\"token\":\"" ++ esc token ++ "\",\"userId\":" ++ show uid ++ "}")
         corsHeaders

------------------------------------------------------------------------
-- Handlers
------------------------------------------------------------------------

-- | POST /api/register
-- Body: {"email":"...","password":"..."}
-- Returns: {"token":"...", "userId":N}
-- Uses walModify for atomic email-uniqueness check + user creation.
handleRegister : String → WalHandle AppState AppOp → HttpRequest → IO HttpResponse
handleRegister secret wal req =
  let body = reqBody req
  in case (jsonGetField "email" body , jsonGetField "password" body) of λ where
    (nothing , _) → pure (mkResponseH 400 "{\"error\":\"Missing email\"}" corsHeaders)
    (_ , nothing) → pure (mkResponseH 400 "{\"error\":\"Missing password\"}" corsHeaders)
    (just email , just password) →
      if not (isValidEmail email)
      then pure (mkResponseH 400 "{\"error\":\"Invalid email\"}" corsHeaders)
      else if not (isValidPassword password)
      then pure (mkResponseH 400 "{\"error\":\"Password must be at least 8 characters\"}" corsHeaders)
      else
        hashPassword password >>= λ hash →
        walModify wal (λ state →
          case findUserByEmail email state of λ where
            (just _) → nothing
            nothing  → just (AddUser (mkUserRecord (allocUserId state) email hash Student))
        ) >>= λ where
          nothing → pure (mkResponseH 409 "{\"error\":\"Email already registered\"}" corsHeaders)
          (just state') →
            case findUserByEmail email state' of λ where
              nothing → pure (mkResponseH 500 "{\"error\":\"Internal error\"}" corsHeaders)
              (just user) →
                let token = mkToken secret (urId user) email (urRole user)
                in pure (mkAuthResp 201 token (urId user))
  where open import Data.Bool using (not; if_then_else_)

private
  loginUser : String → ℕ → String → UserRecord → String → IO HttpResponse
  loginUser secret uid email user password with verifyPassword password (urPassHash user)
  ... | false = pure (mkResponseH 401 "{\"error\":\"Invalid credentials\"}" corsHeaders)
  ... | true  =
    let token = mkToken secret uid email (urRole user)
    in pure (mkAuthResp 200 token uid)

-- | POST /api/login
-- Body: {"email":"...","password":"..."}
-- Returns: {"token":"...", "userId":N}
handleLogin : String → WalHandle AppState AppOp → HttpRequest → IO HttpResponse
handleLogin secret wal req =
  let body = reqBody req
  in case (jsonGetField "email" body , jsonGetField "password" body) of λ where
    (nothing , _) → pure (mkResponseH 400 "{\"error\":\"Missing email\"}" corsHeaders)
    (_ , nothing) → pure (mkResponseH 400 "{\"error\":\"Missing password\"}" corsHeaders)
    (just email , just password) →
      walRead wal >>= λ state →
      case findUserByEmail email state of λ where
        nothing → pure (mkResponseH 401 "{\"error\":\"Invalid credentials\"}" corsHeaders)
        (just user) → loginUser secret (urId user) email user password
