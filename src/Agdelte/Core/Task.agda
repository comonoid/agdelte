{-# OPTIONS --without-K #-}

-- Task: composable asynchronous operations (monad)
-- Used for request chains and complex effect logic
-- Simple cases use Cmd directly

module Agdelte.Core.Task where

open import Data.String using (String)
open import Data.List using (List)
open import Data.Product using (_×_)
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
showHttpError (networkError msg) = "Network error: " ++ msg
  where open import Data.String using (_++_)
showHttpError (httpStatus code msg) = "HTTP " ++ code ++ ": " ++ msg
  where open import Data.String using (_++_)
showHttpError timeout = "Request timeout"
showHttpError (parseError msg) = "Parse error: " ++ msg
  where open import Data.String using (_++_)

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

  -- HTTP with custom headers
  httpGetH : String → List (String × String) → (String → Task A) → (String → Task A) → Task A
  httpPostH : String → List (String × String) → String → (String → Task A) → (String → Task A) → Task A

  -- Fetch URL as ArrayBuffer, return base64-encoded String
  fetchArrayBuffer : String → (String → Task A) → (String → Task A) → Task A

  -- AES-128-CBC decryption via crypto.subtle
  -- key (base64), iv (base64), data (base64) → decrypted (base64)
  decryptAES128 : String → String → String → (String → Task A) → (String → Task A) → Task A

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
-- Error-terminal: on HTTP failure, the error handler does NOT continue through f.
-- This is the expected default — errors stop the pipeline.
-- WARNING: the original onErr handler is REPLACED with `fail e`, not preserved.
-- Any recovery logic in onErr (e.g. `pure defaultValue`) is silently discarded.
-- Use _>>=+_ to preserve error handlers, or `recover` before binding.
_>>=_ : Task A → (A → Task B) → Task B
pure a >>= f = f a
fail e >>= f = fail e
httpGet url onOk onErr >>= f = httpGet url (λ s → onOk s >>= f) (λ e → fail e)
httpPost url body onOk onErr >>= f = httpPost url body (λ s → onOk s >>= f) (λ e → fail e)
httpGetH url hdrs onOk onErr >>= f = httpGetH url hdrs (λ s → onOk s >>= f) (λ e → fail e)
httpPostH url hdrs body onOk onErr >>= f = httpPostH url hdrs body (λ s → onOk s >>= f) (λ e → fail e)
fetchArrayBuffer url onOk onErr >>= f = fetchArrayBuffer url (λ s → onOk s >>= f) (λ e → fail e)
decryptAES128 k iv d onOk onErr >>= f = decryptAES128 k iv d (λ s → onOk s >>= f) (λ e → fail e)

infixl 1 _>>=_ _>>=+_

-- bind with error-preserving semantics: onErr is threaded through f, so
-- side effects in error handlers (logging, cleanup) execute on failure
-- and the result continues through the pipeline.
-- Use when you need error recovery with continuation.
_>>=+_ : Task A → (A → Task B) → Task B
pure a >>=+ f = f a
fail e >>=+ f = fail e
httpGet url onOk onErr >>=+ f = httpGet url (λ s → onOk s >>=+ f) (λ e → onErr e >>=+ f)
httpPost url body onOk onErr >>=+ f = httpPost url body (λ s → onOk s >>=+ f) (λ e → onErr e >>=+ f)
httpGetH url hdrs onOk onErr >>=+ f = httpGetH url hdrs (λ s → onOk s >>=+ f) (λ e → onErr e >>=+ f)
httpPostH url hdrs body onOk onErr >>=+ f = httpPostH url hdrs body (λ s → onOk s >>=+ f) (λ e → onErr e >>=+ f)
fetchArrayBuffer url onOk onErr >>=+ f = fetchArrayBuffer url (λ s → onOk s >>=+ f) (λ e → onErr e >>=+ f)
decryptAES128 k iv d onOk onErr >>=+ f = decryptAES128 k iv d (λ s → onOk s >>=+ f) (λ e → onErr e >>=+ f)

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

-- HTTP GET with headers
httpH : String → List (String × String) → Task String
httpH url hdrs = httpGetH url hdrs pure fail

-- HTTP POST with headers
httpPostH′ : String → List (String × String) → String → Task String
httpPostH′ url hdrs body = httpPostH url hdrs body pure fail

-- Fetch as ArrayBuffer (returns base64)
fetchBinary : String → Task String
fetchBinary url = fetchArrayBuffer url pure fail

-- Decrypt AES-128-CBC (key, iv, data all base64; returns base64)
decrypt : String → String → String → Task String
decrypt key iv dat = decryptAES128 key iv dat pure fail

------------------------------------------------------------------------
-- Error handling
------------------------------------------------------------------------

-- | Run task for side effects, then ALWAYS continue with fallback.
-- Unlike _>>=+_ which stops on `fail`, this replaces `fail` with the
-- continuation, ensuring the fallback always executes.
private
  alwaysThen : Task A → Task B → Task B
  alwaysThen (pure _)                 k = k
  alwaysThen (fail _)                 k = k
  alwaysThen (httpGet u onOk onEr)    k = httpGet u (λ s → alwaysThen (onOk s) k) (λ e → alwaysThen (onEr e) k)
  alwaysThen (httpPost u b onOk onEr) k = httpPost u b (λ s → alwaysThen (onOk s) k) (λ e → alwaysThen (onEr e) k)
  alwaysThen (httpGetH u h onOk onEr) k = httpGetH u h (λ s → alwaysThen (onOk s) k) (λ e → alwaysThen (onEr e) k)
  alwaysThen (httpPostH u h b onOk onEr) k = httpPostH u h b (λ s → alwaysThen (onOk s) k) (λ e → alwaysThen (onEr e) k)
  alwaysThen (fetchArrayBuffer u onOk onEr) k = fetchArrayBuffer u (λ s → alwaysThen (onOk s) k) (λ e → alwaysThen (onEr e) k)
  alwaysThen (decryptAES128 ki iv d onOk onEr) k = decryptAES128 ki iv d (λ s → alwaysThen (onOk s) k) (λ e → alwaysThen (onEr e) k)

-- | Alternative with side-effect preservation: on error, run original
-- onErr for its effects, THEN continue with the fallback task.
-- The result of onErr is discarded (only t₂'s result matters).
-- The fallback always executes regardless of whether onErr calls `fail`.
_<|>_ : Task A → Task A → Task A
pure a <|> _ = pure a
fail _ <|> t₂ = t₂
httpGet url onOk onErr <|> t₂ = httpGet url onOk (λ e → alwaysThen (onErr e) t₂)
httpPost url body onOk onErr <|> t₂ = httpPost url body onOk (λ e → alwaysThen (onErr e) t₂)
httpGetH url hdrs onOk onErr <|> t₂ = httpGetH url hdrs onOk (λ e → alwaysThen (onErr e) t₂)
httpPostH url hdrs body onOk onErr <|> t₂ = httpPostH url hdrs body onOk (λ e → alwaysThen (onErr e) t₂)
fetchArrayBuffer url onOk onErr <|> t₂ = fetchArrayBuffer url onOk (λ e → alwaysThen (onErr e) t₂)
decryptAES128 k iv d onOk onErr <|> t₂ = decryptAES128 k iv d onOk (λ e → alwaysThen (onErr e) t₂)

infixl 3 _<|>_ _<|>!_

-- | Error-dropping alternative: replaces onErr entirely with fallback.
-- Side effects in the original error handler will NOT execute.
-- Use the default _<|>_ if you need error handler preservation.
_<|>!_ : Task A → Task A → Task A
pure a <|>! _ = pure a
fail _ <|>! t₂ = t₂
httpGet url onOk onErr <|>! t₂ = httpGet url onOk (λ _ → t₂)
httpPost url body onOk onErr <|>! t₂ = httpPost url body onOk (λ _ → t₂)
httpGetH url hdrs onOk onErr <|>! t₂ = httpGetH url hdrs onOk (λ _ → t₂)
httpPostH url hdrs body onOk onErr <|>! t₂ = httpPostH url hdrs body onOk (λ _ → t₂)
fetchArrayBuffer url onOk onErr <|>! t₂ = fetchArrayBuffer url onOk (λ _ → t₂)
decryptAES128 k iv d onOk onErr <|>! t₂ = decryptAES128 k iv d onOk (λ _ → t₂)

-- | Recover from immediate failures. Converts `fail e` and HTTP
-- error callbacks to `pure (f e)`. Does NOT affect nested failures
-- inside onOk continuations — those propagate unchanged.
-- WARNING: `recover task handler` still fails if `onOk` internally
-- calls `fail`. Only the direct `onErr` is intercepted.
recover : Task A → (String → A) → Task A
recover (pure a) _ = pure a
recover (fail e) f = pure (f e)
recover (httpGet url onOk onErr) f = httpGet url onOk (λ e → pure (f e))
recover (httpPost url body onOk onErr) f = httpPost url body onOk (λ e → pure (f e))
recover (httpGetH url hdrs onOk onErr) f = httpGetH url hdrs onOk (λ e → pure (f e))
recover (httpPostH url hdrs body onOk onErr) f = httpPostH url hdrs body onOk (λ e → pure (f e))
recover (fetchArrayBuffer url onOk onErr) f = fetchArrayBuffer url onOk (λ e → pure (f e))
recover (decryptAES128 k iv d onOk onErr) f = decryptAES128 k iv d onOk (λ e → pure (f e))

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
  httpGet url (λ s → toResult (onOk s)) (λ e → toResult (onErr e))
toResult (httpPost url body onOk onErr) =
  httpPost url body (λ s → toResult (onOk s)) (λ e → toResult (onErr e))
toResult (httpGetH url hdrs onOk onErr) =
  httpGetH url hdrs (λ s → toResult (onOk s)) (λ e → toResult (onErr e))
toResult (httpPostH url hdrs body onOk onErr) =
  httpPostH url hdrs body (λ s → toResult (onOk s)) (λ e → toResult (onErr e))
toResult (fetchArrayBuffer url onOk onErr) =
  fetchArrayBuffer url (λ s → toResult (onOk s)) (λ e → toResult (onErr e))
toResult (decryptAES128 k iv d onOk onErr) =
  decryptAES128 k iv d (λ s → toResult (onOk s)) (λ e → toResult (onErr e))
