{-# OPTIONS --without-K --guardedness #-}

-- Auth request handlers: register, login.
-- Uses in-memory user store via IORef (WAL persistence added separately).

module Agdelte.Auth.Handler where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Bool using (if_then_else_)
open import Data.String using (_++_; _≟_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)

open import Agdelte.FFI.Server using
  ( HttpRequest; HttpResponse
  ; reqBody; mkResponse; mkResponseH
  ; IORef; newIORef; readIORef; writeIORef
  ; _>>=_; _>>_; pure
  )
open import Agdelte.FFI.Crypto using (hashPassword; verifyPassword)
open import Agdelte.Auth.JWT using (signJWT)
open import Agdelte.Auth.Middleware using (corsHeaders)

------------------------------------------------------------------------
-- User record (in-memory)
------------------------------------------------------------------------

record User : Set where
  constructor mkUser
  field
    userId       : String
    userEmail    : String
    userPassHash : String

open User public

------------------------------------------------------------------------
-- User store (List in IORef)
------------------------------------------------------------------------

UserStore : Set
UserStore = IORef (List User)

newUserStore : IO UserStore
newUserStore = newIORef []

------------------------------------------------------------------------
-- JSON helpers (minimal, for auth endpoints)
------------------------------------------------------------------------

-- Extract field from simple JSON: {"field":"value",...}
-- Minimal parser — handles string fields only, no nesting.
postulate
  jsonGetField : String → String → Maybe String

{-# FOREIGN GHC
  import qualified Data.Text as T

  -- Minimal JSON field extractor (string values only, no nesting)
  jsonGetFieldImpl :: T.Text -> T.Text -> Maybe T.Text
  jsonGetFieldImpl fieldName json =
    let needle = "\"" <> fieldName <> "\""
    in case T.breakOn needle json of
         (_, rest)
           | T.null rest -> Nothing
           | otherwise ->
             let afterKey = T.drop (T.length needle) rest
                 afterColon = T.dropWhile (\c -> c == ':' || c == ' ') afterKey
             in if T.null afterColon || T.head afterColon /= '"'
                then Nothing
                else let valStart = T.tail afterColon
                         val = T.takeWhile (/= '"') valStart
                     in Just val
  #-}
{-# COMPILE GHC jsonGetField = jsonGetFieldImpl #-}

------------------------------------------------------------------------
-- Find user by email
------------------------------------------------------------------------

findByEmail : String → List User → Maybe User
findByEmail _ [] = nothing
findByEmail email (u ∷ us) with userEmail u ≟ email
... | yes _ = just u
... | no _  = findByEmail email us

------------------------------------------------------------------------
-- Generate user ID
------------------------------------------------------------------------

postulate
  generateId : IO String

{-# FOREIGN GHC
  import qualified Data.UUID.V4 as UUID
  import qualified Data.UUID as UUID

  generateIdImpl :: IO T.Text
  generateIdImpl = T.pack . UUID.toString <$> UUID.nextRandom
  #-}
{-# COMPILE GHC generateId = generateIdImpl #-}

------------------------------------------------------------------------
-- JSON string escaping
------------------------------------------------------------------------

postulate
  escapeJsonString : String → String

{-# FOREIGN GHC
  escapeJsonStringImpl :: T.Text -> T.Text
  escapeJsonStringImpl = T.concatMap escChar
    where
      escChar '"'  = "\\\""
      escChar '\\' = "\\\\"
      escChar '\n' = "\\n"
      escChar '\r' = "\\r"
      escChar '\t' = "\\t"
      escChar c    = T.singleton c
  #-}
{-# COMPILE GHC escapeJsonString = escapeJsonStringImpl #-}

------------------------------------------------------------------------
-- Handlers
------------------------------------------------------------------------

-- | POST /api/register
-- Body: {"email":"...","password":"..."}
-- Returns: {"token":"...", "userId":"..."}
handleRegister : String → UserStore → HttpRequest → IO HttpResponse
handleRegister secret store req =
  let body = reqBody req
  in case (jsonGetField "email" body , jsonGetField "password" body) of λ where
    (nothing , _) → pure (mkResponseH 400 "{\"error\":\"Missing email\"}" corsHeaders)
    (_ , nothing) → pure (mkResponseH 400 "{\"error\":\"Missing password\"}" corsHeaders)
    (just email , just password) →
      readIORef store >>= λ users →
      case findByEmail email users of λ where
        (just _) → pure (mkResponseH 409 "{\"error\":\"Email already registered\"}" corsHeaders)
        nothing →
          generateId >>= λ uid →
          hashPassword password >>= λ hash →
          let esc = escapeJsonString
              user = mkUser uid email hash
              token = signJWT secret ("{\"sub\":\"" ++ esc uid ++ "\",\"email\":\"" ++ esc email ++ "\"}")
              respBody = "{\"token\":\"" ++ esc token ++ "\",\"userId\":\"" ++ esc uid ++ "\"}"
          in writeIORef store (user ∷ users) >>
             pure (mkResponseH 201 respBody corsHeaders)
  where
    case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
    case x of f = f x

private
  loginUser : String → String → User → String → IO HttpResponse
  loginUser secret email user password with verifyPassword password (userPassHash user)
  ... | false = pure (mkResponseH 401 "{\"error\":\"Invalid credentials\"}" corsHeaders)
  ... | true  =
    let esc = escapeJsonString
        uid = userId user
        token = signJWT secret ("{\"sub\":\"" ++ esc uid ++ "\",\"email\":\"" ++ esc email ++ "\"}")
        respBody = "{\"token\":\"" ++ esc token ++ "\",\"userId\":\"" ++ esc uid ++ "\"}"
    in pure (mkResponseH 200 respBody corsHeaders)

-- | POST /api/login
-- Body: {"email":"...","password":"..."}
-- Returns: {"token":"...", "userId":"..."}
handleLogin : String → UserStore → HttpRequest → IO HttpResponse
handleLogin secret store req =
  let body = reqBody req
  in case (jsonGetField "email" body , jsonGetField "password" body) of λ where
    (nothing , _) → pure (mkResponseH 400 "{\"error\":\"Missing email\"}" corsHeaders)
    (_ , nothing) → pure (mkResponseH 400 "{\"error\":\"Missing password\"}" corsHeaders)
    (just email , just password) →
      readIORef store >>= λ users →
      case findByEmail email users of λ where
        nothing → pure (mkResponseH 401 "{\"error\":\"Invalid credentials\"}" corsHeaders)
        (just user) → loginUser secret email user password
  where
    case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
    case x of f = f x
