{-# OPTIONS --without-K #-}

-- Client-side auth helpers for Agdelte frontend.
-- Token storage (localStorage), auth header construction,
-- and authenticated HTTP request combinators.

module Agdelte.Auth.Client where

open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (Maybe; just; nothing)

open import Agdelte.Core.Cmd as Cmd using
  ( Cmd; ε; _<>_; httpGetH; httpPostH; getItem; setItem; removeItem )

------------------------------------------------------------------------
-- Token storage keys
------------------------------------------------------------------------

private
  tokenKey : String
  tokenKey = "agdelte-auth-token"

------------------------------------------------------------------------
-- Token management commands
------------------------------------------------------------------------

-- | Save auth token to localStorage.
saveToken : ∀ {A} → String → Cmd A
saveToken token = setItem tokenKey token

-- | Remove auth token from localStorage (logout).
clearToken : ∀ {A} → Cmd A
clearToken = removeItem tokenKey

-- | Load auth token from localStorage. Dispatches Maybe String.
loadToken : ∀ {A} → (Maybe String → A) → Cmd A
loadToken handler = getItem tokenKey handler

------------------------------------------------------------------------
-- Auth headers
------------------------------------------------------------------------

-- | Build Authorization header from token.
authHeaders : String → List (String × String)
authHeaders token = ("Authorization" , "Bearer " ++ token) ∷ []

-- | Build auth + JSON content-type headers.
authJsonHeaders : String → List (String × String)
authJsonHeaders token =
    ("Authorization" , "Bearer " ++ token)
  ∷ ("Content-Type" , "application/json")
  ∷ []

------------------------------------------------------------------------
-- Authenticated HTTP requests (Cmd)
------------------------------------------------------------------------

-- | Authenticated GET request.
authGet : ∀ {A} → String → String → (String → A) → (String → A) → Cmd A
authGet url token onOk onErr = httpGetH url (authHeaders token) onOk onErr

-- | Authenticated POST request with JSON body.
authPost : ∀ {A} → String → String → String → (String → A) → (String → A) → Cmd A
authPost url token body onOk onErr = httpPostH url (authJsonHeaders token) body onOk onErr

------------------------------------------------------------------------
-- JSON string escaping (prevent injection)
------------------------------------------------------------------------

postulate
  escapeJson : String → String
{-# COMPILE JS escapeJson = function(s) {
  return s.replace(/\\/g, '\\\\').replace(/"/g, '\\"').replace(/\n/g, '\\n').replace(/\r/g, '\\r').replace(/\t/g, '\\t');
} #-}

------------------------------------------------------------------------
-- Login/Register commands (unauthenticated POST)
------------------------------------------------------------------------

-- | POST to login endpoint. No auth header needed.
loginCmd : ∀ {A} → String → String → String → (String → A) → (String → A) → Cmd A
loginCmd url email password onOk onErr =
  let body = "{\"email\":\"" ++ escapeJson email ++ "\",\"password\":\"" ++ escapeJson password ++ "\"}"
  in httpPostH url (("Content-Type" , "application/json") ∷ []) body onOk onErr

-- | POST to register endpoint. No auth header needed.
registerCmd : ∀ {A} → String → String → String → (String → A) → (String → A) → Cmd A
registerCmd = loginCmd  -- same body format
