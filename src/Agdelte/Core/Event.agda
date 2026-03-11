{-# OPTIONS --without-K #-}

-- Event: discrete events as AST (description of subscriptions)
-- Runtime interprets this description and creates real subscriptions
--
-- Architecture: Event is split into structural combinators (Event) and
-- leaf event sources (Sub). mapE/filterE only handle structural cases,
-- so adding new event sources to Sub doesn't require updating them.

module Agdelte.Core.Event where

open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; if_then_else_; not)
open import Data.String using (String)
open import Agda.Builtin.String using (primStringEquality)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_; id)
open import Data.Float using (Float)

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
    key      : String   -- Key value ("a", "Enter", "ArrowUp")
    code     : String   -- Physical key code ("KeyA", "Enter", "ArrowUp")
    ctrl     : Bool     -- Ctrl/Control modifier
    alt      : Bool     -- Alt/Option modifier
    shift    : Bool     -- Shift modifier
    meta     : Bool     -- Meta/Command/Windows modifier
    repeat   : Bool     -- True if key held down (auto-repeat)
    location : ℕ        -- 0=standard, 1=left, 2=right, 3=numpad

open KeyboardEvent public

------------------------------------------------------------------------
-- MouseEvent
------------------------------------------------------------------------

record MouseEvent : Set where
  constructor mkMouseEvent
  field
    mouseX   : ℕ      -- clientX
    mouseY   : ℕ      -- clientY
    pageX    : ℕ
    pageY    : ℕ
    button   : ℕ      -- 0=left, 1=middle, 2=right
    buttons  : ℕ      -- bit mask

open MouseEvent public

------------------------------------------------------------------------
-- SharedArrayBuffer (opaque handle)
------------------------------------------------------------------------

open import Agdelte.FFI.Shared using (SharedBuffer) public

------------------------------------------------------------------------
-- Spring configuration
------------------------------------------------------------------------

record SpringConfig : Set where
  constructor mkSpringConfig
  field
    position  : Float
    velocity  : Float
    target    : Float
    stiffness : Float
    damping   : Float

open SpringConfig public

------------------------------------------------------------------------
-- BufferHandle (lightweight reference to a buffer in the registry)
------------------------------------------------------------------------

record BufferHandle : Set where
  constructor bufferHandle
  field
    bufferId      : ℕ    -- Registry handle id
    bufferVersion : ℕ    -- Version (incremented when buffer changes)
    bufferWidth   : ℕ    -- Width (for images)
    bufferHeight  : ℕ    -- Height (for images)

open BufferHandle public

------------------------------------------------------------------------
-- Sub: leaf event sources (no Event sub-expressions)
------------------------------------------------------------------------

-- Sub contains all event sources that don't recursively contain Event.
-- Adding a new event source only requires:
--   1. Add constructor to Sub
--   2. Add handler to runtime/events.js interpretSub
-- No changes needed to mapE or filterE.
--
-- MAINTENANCE: when adding a new constructor to Sub, also update:
--   • runtime/events.js  (interpretSub handler)
data Sub (A : Set) : Set where
  -- === Time primitives ===
  interval : ℕ → A → Sub A
  timeout  : ℕ → A → Sub A

  -- === Animation ===
  animationFrame : A → Sub A
  animationFrameWithTime : (Float → A) → Sub A
  springLoop : SpringConfig → (Float → A) → A → Sub A

  -- === Keyboard ===
  onKeyDown : (KeyboardEvent → Maybe A) → Sub A
  onKeyUp   : (KeyboardEvent → Maybe A) → Sub A

  -- === Mouse ===
  onMouseDown  : (MouseEvent → Maybe A) → Sub A
  onMouseUp    : (MouseEvent → Maybe A) → Sub A
  onMouseMove  : (MouseEvent → Maybe A) → Sub A
  onClick      : (MouseEvent → Maybe A) → Sub A

  -- === HTTP ===
  httpGet  : String → (String → A) → (String → A) → Sub A
  httpPost : String → String → (String → A) → (String → A) → Sub A

  -- === WebSocket ===
  wsConnect : String → (WsMsg → A) → Sub A

  -- === Routing ===
  onUrlChange : (String → A) → Sub A

  -- === Web Worker ===
  worker : String → String → (String → A) → (String → A) → Sub A
  workerWithProgress : String → String → (String → A) → (String → A) → (String → A) → Sub A

  -- === Pool workers ===
  poolWorker : ℕ → String → String → (String → A) → (String → A) → Sub A
  poolWorkerWithProgress : ℕ → String → String → (String → A) → (String → A) → (String → A) → Sub A

  -- === Worker channel ===
  workerChannel : String → (String → A) → (String → A) → Sub A

  -- === SharedArrayBuffer ===
  allocShared : ℕ → (SharedBuffer → A) → Sub A
  workerShared : SharedBuffer → String → String → (String → A) → (String → A) → Sub A

  -- === Buffer Registry ===
  allocImage : ℕ → ℕ → (BufferHandle → A) → Sub A
  allocBuffer : ℕ → (BufferHandle → A) → Sub A

------------------------------------------------------------------------
-- Event: structural combinators (AST) - stays in Set
------------------------------------------------------------------------

-- Design notes:
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

  -- Leaf event source (see Sub above)
  sub : Sub A → Event A

  -- === Combinators ===
  merge    : Event A → Event A → Event A
  debounce : ℕ → Event A → Event A
  throttle : ℕ → Event A → Event A

  -- === Stateful combinators ===
  foldE : ∀ {B : Set} → A → (B → A → A) → Event B → Event A
  mapFilterE : ∀ {B : Set} → (B → Maybe A) → Event B → Event A
  switchE : Event A → Event (Event A) → Event A

  -- === Concurrency ===
  parallel : ∀ {B : Set} → List (Event B) → (List B → A) → Event A
  race : List (Event A) → Event A

------------------------------------------------------------------------
-- Backward-compatible smart constructors for Sub
------------------------------------------------------------------------

-- These wrap Sub constructors in Event, preserving the old API.
-- User code using `interval 1000 msg` works unchanged.

interval : ℕ → A → Event A
interval n a = sub (Sub.interval n a)

timeout : ℕ → A → Event A
timeout n a = sub (Sub.timeout n a)

animationFrame : A → Event A
animationFrame a = sub (Sub.animationFrame a)

animationFrameWithTime : (Float → A) → Event A
animationFrameWithTime h = sub (Sub.animationFrameWithTime h)

springLoop : SpringConfig → (Float → A) → A → Event A
springLoop cfg onTick onSettled = sub (Sub.springLoop cfg onTick onSettled)

onKeyDown : (KeyboardEvent → Maybe A) → Event A
onKeyDown h = sub (Sub.onKeyDown h)

onKeyUp : (KeyboardEvent → Maybe A) → Event A
onKeyUp h = sub (Sub.onKeyUp h)

onMouseDown : (MouseEvent → Maybe A) → Event A
onMouseDown h = sub (Sub.onMouseDown h)

onMouseUp : (MouseEvent → Maybe A) → Event A
onMouseUp h = sub (Sub.onMouseUp h)

onMouseMove : (MouseEvent → Maybe A) → Event A
onMouseMove h = sub (Sub.onMouseMove h)

onClick : (MouseEvent → Maybe A) → Event A
onClick h = sub (Sub.onClick h)

httpGet : String → (String → A) → (String → A) → Event A
httpGet url onOk onErr = sub (Sub.httpGet url onOk onErr)

httpPost : String → String → (String → A) → (String → A) → Event A
httpPost url body onOk onErr = sub (Sub.httpPost url body onOk onErr)

wsConnect : String → (WsMsg → A) → Event A
wsConnect url h = sub (Sub.wsConnect url h)

onUrlChange : (String → A) → Event A
onUrlChange h = sub (Sub.onUrlChange h)

worker : String → String → (String → A) → (String → A) → Event A
worker url input onOk onErr = sub (Sub.worker url input onOk onErr)

workerWithProgress : String → String → (String → A) → (String → A) → (String → A) → Event A
workerWithProgress url input onProg onRes onErr = sub (Sub.workerWithProgress url input onProg onRes onErr)

poolWorker : ℕ → String → String → (String → A) → (String → A) → Event A
poolWorker n url input onOk onErr = sub (Sub.poolWorker n url input onOk onErr)

poolWorkerWithProgress : ℕ → String → String → (String → A) → (String → A) → (String → A) → Event A
poolWorkerWithProgress n url input onProg onRes onErr = sub (Sub.poolWorkerWithProgress n url input onProg onRes onErr)

workerChannel : String → (String → A) → (String → A) → Event A
workerChannel url onMsg onErr = sub (Sub.workerChannel url onMsg onErr)

allocShared : ℕ → (SharedBuffer → A) → Event A
allocShared n h = sub (Sub.allocShared n h)

workerShared : SharedBuffer → String → String → (String → A) → (String → A) → Event A
workerShared buf url input onOk onErr = sub (Sub.workerShared buf url input onOk onErr)

allocImage : ℕ → ℕ → (BufferHandle → A) → Event A
allocImage w h handler = sub (Sub.allocImage w h handler)

allocBuffer : ℕ → (BufferHandle → A) → Event A
allocBuffer n handler = sub (Sub.allocBuffer n handler)

------------------------------------------------------------------------
-- mapE - only handles structural constructors
------------------------------------------------------------------------

-- Leaf events (sub) are wrapped in mapFilterE, so adding new Sub
-- constructors never requires updating mapE.
{-# TERMINATING #-}
mapE : (A → B) → Event A → Event B
mapE f never = never
mapE f (sub s) = mapFilterE (λ a → just (f a)) (sub s)
mapE f (merge e₁ e₂) = merge (mapE f e₁) (mapE f e₂)
mapE f (debounce n e) = debounce n (mapE f e)
mapE f (throttle n e) = throttle n (mapE f e)
mapE f (foldE a₀ step inner) = mapFilterE (λ a → just (f a)) (foldE a₀ step inner)
mapE f (mapFilterE g inner) = mapFilterE (λ x → Data.Maybe.map f (g x)) inner
  where import Data.Maybe
mapE f (switchE initial meta) = switchE (mapE f initial) (mapE (mapE f) meta)
mapE f (parallel es g) = parallel es (f ∘ g)
mapE f (race es) = race (map (mapE f) es)

------------------------------------------------------------------------
-- filterE - only handles structural constructors
------------------------------------------------------------------------

-- Leaf events (sub) are wrapped in mapFilterE, so adding new Sub
-- constructors never requires updating filterE.
{-# TERMINATING #-}
filterE : (A → Bool) → Event A → Event A
filterE p never = never
filterE p (sub s) = mapFilterE (λ a → if p a then just a else nothing) (sub s)
filterE p (merge e₁ e₂) = merge (filterE p e₁) (filterE p e₂)
filterE p (debounce n e) = debounce n (filterE p e)
filterE p (throttle n e) = throttle n (filterE p e)
filterE p (foldE a₀ step inner) =
  mapFilterE (λ a → if p a then just a else nothing) (foldE a₀ step inner)
filterE p (mapFilterE g inner) =
  mapFilterE (λ x → filterMaybe p (g x)) inner
filterE p (switchE initial meta) =
  switchE (filterE p initial) (mapE (filterE p) meta)
filterE p (parallel es g) =
  mapFilterE (λ a → if p a then just a else nothing) (parallel es g)
filterE p (race es) = race (map (filterE p) es)

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
-- Convenient constructors for mouse
------------------------------------------------------------------------

-- Mouse position as (ℕ × ℕ)
Position : Set
Position = ℕ × ℕ

-- Left click (button 0)
onLeftClick : A → Event A
onLeftClick msg = onClick (λ e → if button e ≡ᵇ 0 then just msg else nothing)
  where open import Data.Nat using (_≡ᵇ_)

-- Right click (button 2)
onRightClick : A → Event A
onRightClick msg = onClick (λ e → if button e ≡ᵇ 2 then just msg else nothing)
  where open import Data.Nat using (_≡ᵇ_)

-- Mouse position tracking (simplified: just x,y)
mousePosition : (Position → A) → Event A
mousePosition f = onMouseMove (λ e → just (f (mouseX e , mouseY e)))

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
-- Stateful combinators
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

-- partitionE: split event by predicate into (matches, non-matches)
partitionE : (A → Bool) → Event A → Event A × Event A
partitionE p e = (filterE p e , filterE (not ∘ p) e)

-- leftmost: priority merge — first non-empty event wins
-- In async runtime, equivalent to mergeAll (no simultaneous dispatch)
leftmost : List (Event A) → Event A
leftmost = mergeAll

------------------------------------------------------------------------
-- Concurrency combinators
------------------------------------------------------------------------

-- Collect all results into a list
parallelAll : List (Event A) → Event (List A)
parallelAll es = parallel es id

-- Race with timeout: run event, if no result within N ms, fire fallback
raceTimeout : ℕ → A → Event A → Event A
raceTimeout ms fallback e = race (e ∷ timeout ms fallback ∷ [])

------------------------------------------------------------------------
-- Periodic events
------------------------------------------------------------------------

everySecond : A → Event A
everySecond msg = interval 1000 msg

everyMinute : A → Event A
everyMinute msg = interval 60000 msg

------------------------------------------------------------------------
-- Sequential / monadic combinators
------------------------------------------------------------------------

-- Immediate one-shot event: fires once with value, then done
-- Equivalent to timeout 0 — dispatches on next tick
occur : A → Event A
occur a = timeout 0 a

-- Delay by N ms, then fire unit
delay : ℕ → Event ⊤
delay ms = timeout ms tt

-- Event bind: on each value from e, switch to f(value)
-- For one-shot events (timeout, worker, httpGet): sequential composition
-- For repeated events (interval): switches to latest f(a), canceling previous
infixl 1 _>>=E_

_>>=E_ : Event A → (A → Event B) → Event B
e >>=E f = switchE never (mapE f e)

-- | Sequential execution of ONE-SHOT events, collecting results in order.
-- sequence [e₁, e₂, e₃] fires e₁, then e₂, then e₃, dispatches [r₁, r₂, r₃]
-- IMPORTANT: Only correct for events that fire exactly once (timeout, httpGet,
-- worker). For repeated events (interval, onKeyDown), each new firing of an
-- earlier event DISCARDS all progress from subsequent events via switchE.
-- Use `parallel` for collecting results from repeated event sources.
sequenceE : List (Event A) → Event (List A)
sequenceE []       = occur []
sequenceE (e ∷ es) = e >>=E λ a → mapE (a ∷_) (sequenceE es)
