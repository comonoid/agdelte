{-# OPTIONS --without-K #-}

-- Cmd: commands (side effects)
-- Unlike Event (subscriptions), Cmd executes when a message is dispatched

module Agdelte.Core.Cmd where

open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe)
open import Data.Bool using (Bool; true; false)
open import Function using (_∘_)

open import Agdelte.Core.Task as Task using (Task; Result; ok; err)
open import Agdelte.Core.Event using (BufferHandle)

private
  variable
    A B : Set

------------------------------------------------------------------------
-- Cmd — commands for side effects
------------------------------------------------------------------------

data Cmd (A : Set) : Set where
  -- Empty command
  ε : Cmd A

  -- Command composition (executed in parallel)
  _<>_ : Cmd A → Cmd A → Cmd A

  -- Delayed message (fires after N milliseconds)
  delay : ℕ → A → Cmd A

  -- HTTP requests (one-shot commands, fire once per dispatch)
  -- For persistent subscriptions (polling), use Event.httpGet / Event.httpPost.
  httpGet  : String → (String → A) → (String → A) → Cmd A
  httpPost : String → String → (String → A) → (String → A) → Cmd A

  -- Run Task (monadic API)
  attempt : Task String → (Result String String → A) → Cmd A

  -- === DOM effects ===
  focus     : String → Cmd A                    -- CSS selector
  blur      : String → Cmd A                    -- CSS selector
  scrollTo  : ℕ → ℕ → Cmd A                     -- x, y
  scrollIntoView : String → Cmd A              -- CSS selector

  -- === Clipboard ===
  writeClipboard : String → Cmd A
  readClipboard  : (String → A) → Cmd A

  -- === LocalStorage ===
  getItem : String → (Maybe String → A) → Cmd A
  setItem : String → String → Cmd A
  removeItem : String → Cmd A

  -- === WebSocket ===
  wsSend : String → String → Cmd A              -- url, message

  -- === Worker channel ===
  channelSend : String → String → Cmd A         -- scriptUrl, message

  -- === Buffer Registry ===
  freeBuffer  : BufferHandle → Cmd A
  touchBuffer : BufferHandle → (BufferHandle → A) → Cmd A

  -- === Routing ===
  pushUrl    : String → Cmd A
  replaceUrl : String → Cmd A
  back       : Cmd A
  forward    : Cmd A

infixr 5 _<>_

------------------------------------------------------------------------
-- Functor operations
------------------------------------------------------------------------

mapCmd : (A → B) → Cmd A → Cmd B
mapCmd f ε = ε
mapCmd f (c₁ <> c₂) = mapCmd f c₁ <> mapCmd f c₂
mapCmd f (delay ms msg) = delay ms (f msg)
mapCmd f (httpGet url onOk onErr) = httpGet url (f ∘ onOk) (f ∘ onErr)
mapCmd f (httpPost url body onOk onErr) = httpPost url body (f ∘ onOk) (f ∘ onErr)
mapCmd f (attempt task handler) = attempt task (f ∘ handler)
-- DOM effects (no message)
mapCmd f (focus sel) = focus sel
mapCmd f (blur sel) = blur sel
mapCmd f (scrollTo x y) = scrollTo x y
mapCmd f (scrollIntoView sel) = scrollIntoView sel
-- Clipboard
mapCmd f (writeClipboard s) = writeClipboard s
mapCmd f (readClipboard h) = readClipboard (f ∘ h)
-- LocalStorage
mapCmd f (getItem key h) = getItem key (f ∘ h)
mapCmd f (setItem key val) = setItem key val
mapCmd f (removeItem key) = removeItem key
-- WebSocket
mapCmd f (wsSend url msg) = wsSend url msg
-- Worker channel
mapCmd f (channelSend url msg) = channelSend url msg
-- Buffer Registry
mapCmd f (freeBuffer h) = freeBuffer h
mapCmd f (touchBuffer h handler) = touchBuffer h (f ∘ handler)
-- Routing
mapCmd f (pushUrl url) = pushUrl url
mapCmd f (replaceUrl url) = replaceUrl url
mapCmd f back = back
mapCmd f forward = forward

------------------------------------------------------------------------
-- Combinators
------------------------------------------------------------------------

-- Batch from list of commands
batch : List (Cmd A) → Cmd A
batch [] = ε
batch (c ∷ cs) = c <> batch cs

-- Propositional emptiness predicate (recursive through _<>_)
IsEmpty : Cmd A → Set
IsEmpty ε = ⊤
  where open import Data.Unit using (⊤)
IsEmpty (c₁ <> c₂) = IsEmpty c₁ × IsEmpty c₂
  where open import Data.Product using (_×_)
IsEmpty _ = ⊥
  where open import Data.Empty using (⊥)

-- Boolean emptiness check (for runtime optimization, recursive through _<>_)
isEmpty : Cmd A → Bool
isEmpty ε = true
isEmpty (c₁ <> c₂) = isEmpty c₁ ∧ isEmpty c₂
  where open import Data.Bool using (_∧_)
isEmpty _ = false

------------------------------------------------------------------------
-- Agent interaction combinators
-- Semantic wrappers for communicating with remote Agent servers
------------------------------------------------------------------------

-- Query agent state (GET /agent-path/state)
agentQuery : String → (String → A) → (String → A) → Cmd A
agentQuery endpoint = httpGet endpoint

-- Step agent with input (POST /agent-path/step)
agentStep : String → String → (String → A) → (String → A) → Cmd A
agentStep endpoint input = httpPost endpoint input

-- Step agent without meaningful input (POST /agent-path/step, empty body)
agentStep! : String → (String → A) → (String → A) → Cmd A
agentStep! endpoint = httpPost endpoint ""
