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
-- Escape backslash/quote and ALL control characters (U+0000–U+001F) as \u00XX.
-- Escaping only \n\r\t leaves other control chars raw → invalid JSON / smuggling.
{-# COMPILE JS escapeJson = function(s) {
  return s.replace(/[\u0000-\u001f\\"]/g, function(ch) {
    switch (ch) {
      case '\\': return '\\\\';
      case '"':  return '\\"';
      case '\n': return '\\n';
      case '\r': return '\\r';
      case '\t': return '\\t';
      case '\b': return '\\b';
      case '\f': return '\\f';
      default:   return '\\u' + ch.charCodeAt(0).toString(16).padStart(4, '0');
    }
  });
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
