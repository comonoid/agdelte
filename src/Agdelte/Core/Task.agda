{-# OPTIONS --without-K #-}

-- Task: composable asynchronous operations (monad)
-- Used for request chains and complex effect logic
-- Simple cases use Cmd directly

module Agdelte.Core.Task where

open import Data.String using (String)
open import Function using (_∘_; id)

private
  variable
    A B C : Set

------------------------------------------------------------------------
-- Result — result with possible error
------------------------------------------------------------------------

data Result (E A : Set) : Set where
  ok  : A → Result E A
  err : E → Result E A

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

-- Alternative on error
_<|>_ : Task A → Task A → Task A
pure a <|> _ = pure a
fail _ <|> t₂ = t₂
httpGet url onOk onErr <|> t₂ = httpGet url onOk (λ _ → t₂)
httpPost url body onOk onErr <|> t₂ = httpPost url body onOk (λ _ → t₂)

infixl 3 _<|>_

-- Recover: turn error into value
recover : Task A → (String → A) → Task A
recover (pure a) _ = pure a
recover (fail e) f = pure (f e)
recover (httpGet url onOk onErr) f = httpGet url onOk (λ e → pure (f e))
recover (httpPost url body onOk onErr) f = httpPost url body onOk (λ e → pure (f e))

------------------------------------------------------------------------
-- Result conversion
------------------------------------------------------------------------

-- Get Result instead of fail
toResult : Task A → Task (Result String A)
toResult t = (ok <$> t) <|> (recover (fail "") (λ e → err e))
  -- Simplified version
