{-# OPTIONS --without-K #-}

-- Core Event types: WsMsg, KeyboardEvent, MouseEvent, Sub, Event, mapE, filterE.
-- Re-exported by Agdelte.Core.Event for backward compatibility.

module Agdelte.Core.Event.Core where

open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; if_then_else_; not; _∧_)
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

------------------------------------------------------------------------
-- WebSocket Message
------------------------------------------------------------------------

data WsMsg : Set where
  WsConnected : WsMsg
  WsMessage   : String → WsMsg
  WsBinary    : String → WsMsg
  WsClosed    : WsMsg
  WsError     : String → WsMsg

------------------------------------------------------------------------
-- KeyboardEvent
------------------------------------------------------------------------

record KeyboardEvent : Set where
  constructor mkKeyboardEvent
  field
    key      : String
    code     : String
    ctrl     : Bool
    alt      : Bool
    shift    : Bool
    meta     : Bool
    repeat   : Bool
    location : ℕ

open KeyboardEvent public

------------------------------------------------------------------------
-- MouseEvent
------------------------------------------------------------------------

record MouseEvent : Set where
  constructor mkMouseEvent
  field
    mouseX   : Float
    mouseY   : Float
    pageX    : Float
    pageY    : Float
    button   : ℕ
    buttons  : ℕ

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
-- BufferHandle
------------------------------------------------------------------------

record BufferHandle : Set where
  constructor bufferHandle
  field
    bufferId      : ℕ
    bufferVersion : ℕ
    bufferWidth   : ℕ
    bufferHeight  : ℕ

open BufferHandle public

------------------------------------------------------------------------
-- Sub: leaf event sources
------------------------------------------------------------------------

module SubDef where
  data Sub (A : Set) : Set where
    interval : ℕ → A → Sub A
    timeout  : ℕ → A → Sub A
    animationFrame : A → Sub A
    animationFrameWithTime : (Float → A) → Sub A
    springLoop : SpringConfig → (Float → A) → A → Sub A
    onKeyDown : (KeyboardEvent → Maybe A) → Sub A
    onKeyUp   : (KeyboardEvent → Maybe A) → Sub A
    onMouseDown  : (MouseEvent → Maybe A) → Sub A
    onMouseUp    : (MouseEvent → Maybe A) → Sub A
    onMouseMove  : (MouseEvent → Maybe A) → Sub A
    onClick      : (MouseEvent → Maybe A) → Sub A
    httpGet  : String → (String → A) → (String → A) → Sub A
    httpPost : String → String → (String → A) → (String → A) → Sub A
    wsConnect : String → (WsMsg → A) → Sub A
    onUrlChange : (String → A) → Sub A
    worker : String → String → (String → A) → (String → A) → Sub A
    workerWithProgress : String → String → (String → A) → (String → A) → (String → A) → Sub A
    poolWorker : ℕ → String → String → (String → A) → (String → A) → Sub A
    poolWorkerWithProgress : ℕ → String → String → (String → A) → (String → A) → (String → A) → Sub A
    workerChannel : String → (String → A) → (String → A) → Sub A
    allocShared : ℕ → (SharedBuffer → A) → Sub A
    workerShared : SharedBuffer → String → String → (String → A) → (String → A) → Sub A
    allocImage : ℕ → ℕ → (BufferHandle → A) → Sub A
    allocBuffer : ℕ → (BufferHandle → A) → Sub A
    allocImageE : ℕ → ℕ → (BufferHandle → A) → (String → A) → Sub A
    allocBufferE : ℕ → (BufferHandle → A) → (String → A) → Sub A

open SubDef public using (Sub)

private
  mapMaybe : ∀ {X Y : Set} → (X → Y) → Maybe X → Maybe Y
  mapMaybe g (just x) = just (g x)
  mapMaybe _ nothing  = nothing

mapSub : (A → B) → Sub A → Sub B
mapSub f (Sub.interval n a) = Sub.interval n (f a)
mapSub f (Sub.timeout n a) = Sub.timeout n (f a)
mapSub f (Sub.animationFrame a) = Sub.animationFrame (f a)
mapSub f (Sub.animationFrameWithTime h) = Sub.animationFrameWithTime (f ∘ h)
mapSub f (Sub.springLoop cfg onTick onSettled) = Sub.springLoop cfg (f ∘ onTick) (f onSettled)
mapSub f (Sub.onKeyDown h) = Sub.onKeyDown (λ e → mapMaybe f (h e))
mapSub f (Sub.onKeyUp h) = Sub.onKeyUp (λ e → mapMaybe f (h e))
mapSub f (Sub.onMouseDown h) = Sub.onMouseDown (λ e → mapMaybe f (h e))
mapSub f (Sub.onMouseUp h) = Sub.onMouseUp (λ e → mapMaybe f (h e))
mapSub f (Sub.onMouseMove h) = Sub.onMouseMove (λ e → mapMaybe f (h e))
mapSub f (Sub.onClick h) = Sub.onClick (λ e → mapMaybe f (h e))
mapSub f (Sub.httpGet url onOk onErr) = Sub.httpGet url (f ∘ onOk) (f ∘ onErr)
mapSub f (Sub.httpPost url body onOk onErr) = Sub.httpPost url body (f ∘ onOk) (f ∘ onErr)
mapSub f (Sub.wsConnect url h) = Sub.wsConnect url (f ∘ h)
mapSub f (Sub.onUrlChange h) = Sub.onUrlChange (f ∘ h)
mapSub f (Sub.worker url input onOk onErr) = Sub.worker url input (f ∘ onOk) (f ∘ onErr)
mapSub f (Sub.workerWithProgress url input onProg onRes onErr) = Sub.workerWithProgress url input (f ∘ onProg) (f ∘ onRes) (f ∘ onErr)
mapSub f (Sub.poolWorker n url input onOk onErr) = Sub.poolWorker n url input (f ∘ onOk) (f ∘ onErr)
mapSub f (Sub.poolWorkerWithProgress n url input onProg onRes onErr) = Sub.poolWorkerWithProgress n url input (f ∘ onProg) (f ∘ onRes) (f ∘ onErr)
mapSub f (Sub.workerChannel url onMsg onErr) = Sub.workerChannel url (f ∘ onMsg) (f ∘ onErr)
mapSub f (Sub.allocShared n h) = Sub.allocShared n (f ∘ h)
mapSub f (Sub.workerShared buf url input onOk onErr) = Sub.workerShared buf url input (f ∘ onOk) (f ∘ onErr)
mapSub f (Sub.allocImage w h handler) = Sub.allocImage w h (f ∘ handler)
mapSub f (Sub.allocBuffer n handler) = Sub.allocBuffer n (f ∘ handler)
mapSub f (Sub.allocImageE w h handler onErr) = Sub.allocImageE w h (f ∘ handler) (f ∘ onErr)
mapSub f (Sub.allocBufferE n handler onErr) = Sub.allocBufferE n (f ∘ handler) (f ∘ onErr)

------------------------------------------------------------------------
-- Event: structural combinators (AST)
------------------------------------------------------------------------

{-# NO_POSITIVITY_CHECK #-}
{-# NO_UNIVERSE_CHECK #-}
data Event (A : Set) : Set where
  never : Event A
  sub : Sub A → Event A
  merge    : Event A → Event A → Event A
  debounce : ℕ → Event A → Event A
  throttle : ℕ → Event A → Event A
  foldE : ∀ {B : Set} → A → (B → A → A) → Event B → Event A
  mapFilterE : ∀ {B : Set} → (B → Maybe A) → Event B → Event A
  switchE : Event A → Event (Event A) → Event A
  parallel : ∀ {B : Set} → List (Event B) → (List B → A) → Event A
  race : List (Event A) → Event A

------------------------------------------------------------------------
-- Backward-compatible smart constructors for Sub
------------------------------------------------------------------------

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

allocImageE : ℕ → ℕ → (BufferHandle → A) → (String → A) → Event A
allocImageE w h handler onErr = sub (Sub.allocImageE w h handler onErr)

allocBufferE : ℕ → (BufferHandle → A) → (String → A) → Event A
allocBufferE n handler onErr = sub (Sub.allocBufferE n handler onErr)

------------------------------------------------------------------------
-- mapE / filterE
------------------------------------------------------------------------

mapE : (A → B) → Event A → Event B
mapE f never = never
mapE f e     = mapFilterE (λ a → just (f a)) e

filterE : (A → Bool) → Event A → Event A
filterE p never = never
filterE p e     = mapFilterE (λ a → if p a then just a else nothing) e
