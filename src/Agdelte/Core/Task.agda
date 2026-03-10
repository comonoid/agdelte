{-# OPTIONS --without-K #-}

-- Task: composable asynchronous operations (monad)
-- Used for request chains and complex effect logic
-- Simple cases use Cmd directly

module Agdelte.Core.Task where

open import Data.String using (String)
open import Function using (_∘_; id)

-- Import shared Result type
open import Agdelte.Core.Result using (Result; ok; err) public

private
  variable
    A B C : Set

mapResult : ∀ {E} → (A → B) → Result E A → Result E B
mapResult f (ok a)  = ok (f a)
mapResult f (err e) = err e

------------------------------------------------------------------------
-- HttpError — HTTP errors
------------------------------------------------------------------------

data HttpError : Set where
  networkError : String → HttpError
  httpStatus   : String → String → HttpError  -- code, message
  timeout      : HttpError
  parseError   : String → HttpError

showHttpError : HttpError → String
showHttpError (networkError msg) = "Network error: " Data.String.++ msg
  where open import Data.String
showHttpError (httpStatus code msg) = "HTTP " Data.String.++ code Data.String.++ ": " Data.String.++ msg
  where open import Data.String
showHttpError timeout = "Request timeout"
showHttpError (parseError msg) = "Parse error: " Data.String.++ msg
  where open import Data.String

------------------------------------------------------------------------
-- Task — monad of asynchronous operations (CPS-style)
------------------------------------------------------------------------

-- Task uses continuation-passing style for composition
-- This avoids problems with universe levels

data Task (A : Set) : Set where
  -- Pure value
  pure : A → Task A

  -- Error
  fail : String → Task A

  -- HTTP GET: url, onSuccess continuation, onError continuation
  httpGet : String → (String → Task A) → (String → Task A) → Task A

  -- HTTP POST: url, body, onSuccess continuation, onError continuation
  httpPost : String → String → (String → Task A) → (String → Task A) → Task A

-- httpGet url onOk onErr:
--   onOk receives the response body as String
--   onErr receives an error message (network error description or HTTP status text)
-- httpPost url body onOk onErr:
--   body is sent as request body (text/plain)
--   onOk/onErr — same as httpGet

------------------------------------------------------------------------
-- Monadic operations
------------------------------------------------------------------------

-- bind (>>=)
_>>=_ : Task A → (A → Task B) → Task B
pure a >>= f = f a
fail e >>= f = fail e
httpGet url onOk onErr >>= f = httpGet url (λ s → onOk s >>= f) (λ e → onErr e >>= f)
httpPost url body onOk onErr >>= f = httpPost url body (λ s → onOk s >>= f) (λ e → onErr e >>= f)

infixl 1 _>>=_

-- fmap (<$>)
_<$>_ : (A → B) → Task A → Task B
f <$> t = t >>= (pure ∘ f)

infixl 4 _<$>_

-- then (>>)
_>>_ : Task A → Task B → Task B
ta >> tb = ta >>= λ _ → tb

infixl 1 _>>_

------------------------------------------------------------------------
-- HTTP combinators
------------------------------------------------------------------------

-- Simple HTTP GET (returns result or fail)
http : String → Task String
http url = httpGet url pure fail

-- HTTP POST
httpPost′ : String → String → Task String
httpPost′ url body = httpPost url body pure fail

------------------------------------------------------------------------
-- Error handling
------------------------------------------------------------------------

-- | Alternative combinator: try first task, on error run second.
-- WARNING: replaces the error handler of the first task entirely.
-- The original onErr is discarded — side effects in it (logging,
-- cleanup) will NOT execute on failure. To preserve side effects,
-- use `recover` or manual error handling instead.
_<|>_ : Task A → Task A → Task A
pure a <|> _ = pure a
fail _ <|> t₂ = t₂
httpGet url onOk onErr <|> t₂ = httpGet url onOk (λ _ → t₂)
httpPost url body onOk onErr <|> t₂ = httpPost url body onOk (λ _ → t₂)

infixl 3 _<|>_

-- | Recover from immediate failures. Converts `fail e` and HTTP
-- error callbacks to `pure (f e)`. Does NOT affect nested failures
-- inside onOk continuations — those propagate unchanged.
recover : Task A → (String → A) → Task A
recover (pure a) _ = pure a
recover (fail e) f = pure (f e)
recover (httpGet url onOk onErr) f = httpGet url onOk (λ e → pure (f e))
recover (httpPost url body onOk onErr) f = httpPost url body onOk (λ e → pure (f e))

------------------------------------------------------------------------
-- Result conversion
------------------------------------------------------------------------

-- | Convert Task to Result-producing Task. Top-level `fail` becomes
-- `pure (err e)`. HTTP errors become `err`. Nested tasks inside
-- onOk continuations are also wrapped via recursive call.
-- Note: this is an AST transformation, not runtime error catching.
toResult : Task A → Task (Result String A)
toResult (pure a) = pure (ok a)
toResult (fail e) = pure (err e)
toResult (httpGet url onOk onErr) =
  httpGet url (λ s → toResult (onOk s)) (λ e → pure (err e))
toResult (httpPost url body onOk onErr) =
  httpPost url body (λ s → toResult (onOk s)) (λ e → pure (err e))
