{-# OPTIONS --without-K #-}

-- Event: discrete events as AST (description of subscriptions)
-- Runtime interprets this description and creates real subscriptions

module Agdelte.Core.Event where

open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; if_then_else_)
open import Data.String using (String)
open import Agda.Builtin.String using (primStringEquality)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Function using (_∘_; id)

private
  variable
    A B C : Set

  -- Filter Maybe by predicate (used by filterE)
  filterMaybe : {A : Set} → (A → Bool) → Maybe A → Maybe A
  filterMaybe p nothing  = nothing
  filterMaybe p (just a) = if p a then just a else nothing

  -- Lookup key in association list (used by onKeys, onKeysUp)
  lookupKey : {A : Set} → String → List (String × A) → Maybe A
  lookupKey _ []              = nothing
  lookupKey k ((k' , v) ∷ rest) =
    if primStringEquality k k' then just v else lookupKey k rest

------------------------------------------------------------------------
-- WebSocket Message
------------------------------------------------------------------------

data WsMsg : Set where
  WsConnected : WsMsg
  WsMessage   : String → WsMsg
  WsClosed    : WsMsg
  WsError     : String → WsMsg

------------------------------------------------------------------------
-- KeyboardEvent
------------------------------------------------------------------------

record KeyboardEvent : Set where
  constructor mkKeyboardEvent
  field
    key   : String
    code  : String
    ctrl  : Bool
    alt   : Bool
    shift : Bool
    meta  : Bool

open KeyboardEvent public

------------------------------------------------------------------------
-- Event as data type (AST) - stays in Set
------------------------------------------------------------------------

-- Design notes (Phase 5):
--
-- NO_UNIVERSE_CHECK: foldE and mapFilterE quantify over a hidden type B
-- (∀ {B : Set} → ...), which lifts the constructor to Set₁. But Event
-- must stay in Set so that existing code (records, lists of events) works.
-- Since Event compiles to JS (Scott encoding), universe levels are erased.
--
-- NO_POSITIVITY_CHECK: switchE uses Event (Event A) - Event appears as
-- an argument to itself, violating strict positivity. This is safe here:
-- the runtime interprets the AST, never unfolds it recursively in Agda.
--
-- Why no snapshot or foldp constructors:
-- In ReactiveApp, the model IS the signal, and subs : Model → Event Msg
-- provides model access via closure - snapshot is implicit.
-- The update function IS foldp: update : Msg → Model → Model.
-- Adding separate constructors would duplicate what the architecture
-- already provides, with no runtime benefit.
{-# NO_POSITIVITY_CHECK #-}
{-# NO_UNIVERSE_CHECK #-}
data Event (A : Set) : Set where
  -- Empty event
  never : Event A

  -- === Time primitives ===
  interval : ℕ → A → Event A
  timeout  : ℕ → A → Event A

  -- === Keyboard ===
  -- Handler returns Maybe A (nothing = ignore)
  onKeyDown : (KeyboardEvent → Maybe A) → Event A
  onKeyUp   : (KeyboardEvent → Maybe A) → Event A

  -- === HTTP ===
  httpGet  : String → (String → A) → (String → A) → Event A
  httpPost : String → String → (String → A) → (String → A) → Event A

  -- === WebSocket ===
  -- wsConnect url → Event with messages about connection state
  wsConnect : String → (WsMsg → A) → Event A

  -- === Routing ===
  -- Event on URL change (popstate)
  onUrlChange : (String → A) → Event A

  -- === Web Worker ===
  -- Spawn a worker, send input, receive results
  -- worker scriptUrl input onResult onError
  -- Structured concurrency: unsubscribe terminates the worker
  worker : String → String → (String → A) → (String → A) → Event A

  -- === Combinators ===
  merge    : Event A → Event A → Event A
  debounce : ℕ → Event A → Event A    -- delay after pause
  throttle : ℕ → Event A → Event A    -- rate limiting

  -- === Stateful combinators (Phase 5) ===
  -- foldE: accumulate state across event occurrences
  -- Runtime maintains internal state A; on each B from inner event,
  -- computes new A = step(B, oldA), dispatches new A
  foldE : ∀ {B : Set} → A → (B → A → A) → Event B → Event A

  -- mapFilterE: map + filter in one step (Nothing = skip, Just b = dispatch b)
  mapFilterE : ∀ {B : Set} → (B → Maybe A) → Event B → Event A

  -- switchE: start with first event, switch to new source on each meta-event
  -- Runtime manages current subscription, swaps on meta-event occurrence
  switchE : Event A → Event (Event A) → Event A

------------------------------------------------------------------------
-- mapE - function, not constructor (to keep Event ∈ Set)
------------------------------------------------------------------------

{-# TERMINATING #-}
mapE : (A → B) → Event A → Event B
mapE f never = never
mapE f (interval n a) = interval n (f a)
mapE f (timeout n a) = timeout n (f a)
mapE f (onKeyDown h) = onKeyDown (λ e → Data.Maybe.map f (h e))
  where import Data.Maybe
mapE f (onKeyUp h) = onKeyUp (λ e → Data.Maybe.map f (h e))
  where import Data.Maybe
mapE f (httpGet url onOk onErr) = httpGet url (f ∘ onOk) (f ∘ onErr)
mapE f (httpPost url body onOk onErr) = httpPost url body (f ∘ onOk) (f ∘ onErr)
mapE f (wsConnect url h) = wsConnect url (f ∘ h)
mapE f (onUrlChange h) = onUrlChange (f ∘ h)
mapE f (worker url input onOk onErr) = worker url input (f ∘ onOk) (f ∘ onErr)
mapE f (merge e₁ e₂) = merge (mapE f e₁) (mapE f e₂)
mapE f (debounce n e) = debounce n (mapE f e)
mapE f (throttle n e) = throttle n (mapE f e)
mapE f (foldE a₀ step inner) = mapFilterE (λ a → just (f a)) (foldE a₀ step inner)
mapE f (mapFilterE g inner) = mapFilterE (λ x → Data.Maybe.map f (g x)) inner
  where import Data.Maybe
mapE f (switchE initial meta) = switchE (mapE f initial) (mapE (mapE f) meta)

------------------------------------------------------------------------
-- filterE - through mapE with Maybe
------------------------------------------------------------------------

{-# TERMINATING #-}
filterE : (A → Bool) → Event A → Event A
filterE p never = never
filterE p (interval n a) = if p a then interval n a else never
filterE p (timeout n a) = if p a then timeout n a else never
filterE p (onKeyDown h) = onKeyDown (λ e → filterMaybe p (h e))
filterE p (onKeyUp h) = onKeyUp (λ e → filterMaybe p (h e))
filterE p (httpGet url onOk onErr) = httpGet url onOk onErr  -- filter applied in runtime
filterE p (httpPost url body onOk onErr) = httpPost url body onOk onErr
filterE p (wsConnect url h) = wsConnect url h  -- filter on WsMsg makes no sense
filterE p (onUrlChange h) = onUrlChange h      -- filter on URL makes no sense
filterE p (worker url input onOk onErr) = worker url input onOk onErr  -- filter applied in runtime
filterE p (merge e₁ e₂) = merge (filterE p e₁) (filterE p e₂)
filterE p (debounce n e) = debounce n (filterE p e)
filterE p (throttle n e) = throttle n (filterE p e)
filterE p (foldE a₀ step inner) =
  mapFilterE (λ a → if p a then just a else nothing) (foldE a₀ step inner)
filterE p (mapFilterE g inner) =
  mapFilterE (λ x → filterMaybe p (g x)) inner
filterE p (switchE initial meta) =
  switchE (filterE p initial) (mapE (filterE p) meta)

------------------------------------------------------------------------
-- Convenient constructors for keyboard
------------------------------------------------------------------------

-- Subscribe to specific key (creates one listener)
onKey : String → A → Event A
onKey k msg = onKeyDown (λ e → if primStringEquality k (KeyboardEvent.key e) then just msg else nothing)

-- Subscribe to multiple keys (ONE listener, efficient!)
-- Usage: onKeys (("ArrowUp" , MoveUp) ∷ ("ArrowDown" , MoveDown) ∷ [])
onKeys : List (String × A) → Event A
onKeys pairs = onKeyDown (λ e → lookupKey (KeyboardEvent.key e) pairs)

-- Flexible subscription with predicate (for key combinations)
-- Usage: onKeyWhen (λ e → ctrl e ∧ key e ≡ᵇ "s") Save
onKeyWhen : (KeyboardEvent → Bool) → A → Event A
onKeyWhen pred msg = onKeyDown (λ e → if pred e then just msg else nothing)

-- Combinations with modifiers
onCtrlKey : String → A → Event A
onCtrlKey k msg = onKeyWhen (λ e → ctrl e ∧ primStringEquality k (key e)) msg
  where open import Data.Bool using (_∧_)

onAltKey : String → A → Event A
onAltKey k msg = onKeyWhen (λ e → alt e ∧ primStringEquality k (key e)) msg
  where open import Data.Bool using (_∧_)

onShiftKey : String → A → Event A
onShiftKey k msg = onKeyWhen (λ e → shift e ∧ primStringEquality k (key e)) msg
  where open import Data.Bool using (_∧_)

onMetaKey : String → A → Event A
onMetaKey k msg = onKeyWhen (λ e → meta e ∧ primStringEquality k (key e)) msg
  where open import Data.Bool using (_∧_)

-- Arrows (for convenience, but better to use onKeys for multiple)
onArrowUp : A → Event A
onArrowUp msg = onKey "ArrowUp" msg

onArrowDown : A → Event A
onArrowDown msg = onKey "ArrowDown" msg

onArrowLeft : A → Event A
onArrowLeft msg = onKey "ArrowLeft" msg

onArrowRight : A → Event A
onArrowRight msg = onKey "ArrowRight" msg

-- Special keys
onEnter : A → Event A
onEnter msg = onKey "Enter" msg

onEscape : A → Event A
onEscape msg = onKey "Escape" msg

onSpace : A → Event A
onSpace msg = onKey " " msg

------------------------------------------------------------------------
-- Helpers for keyUp (for tracking simultaneous presses)
------------------------------------------------------------------------

-- Subscribe to releasing specific key
onKeyReleased : String → A → Event A
onKeyReleased k msg = onKeyUp (λ e → if primStringEquality k (KeyboardEvent.key e) then just msg else nothing)

-- Subscribe to releasing multiple keys (one listener)
onKeysUp : List (String × A) → Event A
onKeysUp pairs = onKeyUp (λ e → lookupKey (KeyboardEvent.key e) pairs)

-- Flexible subscription to keyUp with predicate
onKeyUpWhen : (KeyboardEvent → Bool) → A → Event A
onKeyUpWhen pred msg = onKeyUp (λ e → if pred e then just msg else nothing)

------------------------------------------------------------------------
-- Combinators
------------------------------------------------------------------------

-- Merge list of events
mergeAll : List (Event A) → Event A
mergeAll [] = never
mergeAll (e ∷ es) = merge e (mergeAll es)

-- Infix merge
_<|>_ : Event A → Event A → Event A
_<|>_ = merge

infixr 3 _<|>_

-- Infix mapE
_<$>_ : (A → B) → Event A → Event B
_<$>_ = mapE

infixl 4 _<$>_

------------------------------------------------------------------------
-- Stateful combinators (Phase 5)
------------------------------------------------------------------------

-- accumE: apply function events to accumulator, emit result
-- accumE 0 [suc, suc, suc] → [1, 2, 3]
accumE : A → Event (A → A) → Event A
accumE a₀ e = foldE a₀ (λ f a → f a) e

-- mapAccum: map with state, emit projected value
-- On each B from inner, compute (newState, output) = step(B, oldState), emit output
mapAccum : ∀ {S : Set} → (B → S → S × A) → S → Event B → Event A
mapAccum step s₀ e = mapFilterE proj (foldE (s₀ , nothing) step' e)
  where
    open Data.Product using (proj₂)
    step' : _ → _ → _
    step' b (s , _) with step b s
    ... | (s' , a) = (s' , just a)
    proj : _ → Maybe _
    proj (_ , ma) = ma

-- gate: filter event by a predicate on event values (synonym for filterE)
gate : (A → Bool) → Event A → Event A
gate = filterE

------------------------------------------------------------------------
-- Periodic events
------------------------------------------------------------------------

everySecond : A → Event A
everySecond msg = interval 1000 msg

everyMinute : A → Event A
everyMinute msg = interval 60000 msg
