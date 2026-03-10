{-# OPTIONS --without-K --guardedness #-}

-- Request: HTTP requests (Primitive API)
--
-- NOTE: This module uses raw JS objects with a separate runtime path.
-- For the canonical API using Scott-encoded AST interpreted by the
-- standard runtime (events.js), use Core.Event.httpGet/httpPost.

module Agdelte.Primitive.Request where

open import Data.String using (String)
open import Data.List using (List)
open import Data.Product using (_×_)
open import Data.Maybe using (Maybe)
open import Agdelte.Core.Event using (Event)

------------------------------------------------------------------------
-- HTTP Request Types
------------------------------------------------------------------------

-- Request method
data Method : Set where
  GET POST PUT DELETE PATCH : Method

-- Request configuration
record RequestConfig : Set where
  constructor mkRequest
  field
    method  : Method
    url     : String
    body    : Maybe String
    headers : List (String × String)

open RequestConfig public

------------------------------------------------------------------------
-- HTTP Request Events
------------------------------------------------------------------------

postulate
  -- Execute HTTP request
  httpRequest : ∀ {A : Set}
              → RequestConfig
              → (String → A)    -- onSuccess (JSON string)
              → (String → A)    -- onError
              → Event A

  -- GET request
  httpGet : ∀ {A : Set}
          → String           -- URL
          → (String → A)     -- onSuccess
          → (String → A)     -- onError
          → Event A

  -- POST request
  httpPost : ∀ {A : Set}
           → String          -- URL
           → String          -- Body (JSON)
           → (String → A)    -- onSuccess
           → (String → A)    -- onError
           → Event A

{-# COMPILE JS httpRequest = _ => config => onSuccess => onError =>
  config["mkRequest"]({mkRequest: (method, url, body, headers) => {
    const methodStr = method({
      "GET": () => "GET", "POST": () => "POST", "PUT": () => "PUT",
      "DELETE": () => "DELETE", "PATCH": () => "PATCH"
    });
    const bodyStr = body({just: s => s, nothing: () => null});
    const hdrs = {};
    let cur = headers;
    let done = false;
    while (!done) {
      cur({
        '[]': () => { done = true; },
        '_∷_': (pair, rest) => {
          pair({'_,_': (k, v) => { hdrs[k] = v; }});
          cur = rest;
        }
      });
    }
    return {
      type: 'request',
      config: { method: methodStr, url, body: bodyStr, headers: hdrs, onSuccess, onError },
      now: [],
      get next() { return this; }
    };
  }})
#-}

{-# COMPILE JS httpGet = _ => url => onSuccess => onError => ({
  type: 'request',
  config: {
    method: 'GET',
    url,
    onSuccess,
    onError
  },
  now: [],
  get next() { return this; }
}) #-}

{-# COMPILE JS httpPost = _ => url => body => onSuccess => onError => ({
  type: 'request',
  config: {
    method: 'POST',
    url,
    body,
    headers: { 'Content-Type': 'application/json' },
    onSuccess,
    onError
  },
  now: [],
  get next() { return this; }
}) #-}

------------------------------------------------------------------------
-- Utilities
------------------------------------------------------------------------

-- Simple GET without error handling (returns Maybe)
simpleGet : ∀ {A : Set}
          → String
          → (String → A)
          → A              -- Value on error
          → Event A
simpleGet url onSuccess onError =
  httpGet url onSuccess (λ _ → onError)
