{-# OPTIONS --without-K --guardedness #-}

-- Mouse: mouse events (Primitive API)
--
-- NOTE: This module uses raw JS objects with a separate runtime path.
-- For the canonical API using Scott-encoded AST interpreted by the
-- standard runtime (events.js), use Core.Event constructors.

module Agdelte.Primitive.Mouse where

open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; if_then_else_)
open import Data.Product using (_×_; _,_)
open import Agdelte.Core.Event using (Event; mapFilterE)

------------------------------------------------------------------------
-- Mouse Event Data
------------------------------------------------------------------------

record MouseEvent : Set where
  constructor mkMouseEvent
  field
    x       : ℕ      -- clientX
    y       : ℕ      -- clientY
    pageX   : ℕ
    pageY   : ℕ
    button  : ℕ      -- 0=left, 1=middle, 2=right
    buttons : ℕ      -- Bit mask

open MouseEvent public

-- Mouse position
Position : Set
Position = ℕ × ℕ

------------------------------------------------------------------------
-- Mouse Events
------------------------------------------------------------------------

postulate
  -- Mouse movement
  onMouseMove : ∀ {A : Set} → (MouseEvent → A) → Event A

  -- Mouse position (simplified)
  mousePosition : ∀ {A : Set} → (Position → A) → Event A

  -- Clicks
  onMouseDown : ∀ {A : Set} → (MouseEvent → A) → Event A
  onMouseUp : ∀ {A : Set} → (MouseEvent → A) → Event A
  onGlobalClick : ∀ {A : Set} → (MouseEvent → A) → Event A

{-# COMPILE JS onMouseMove = _ => handler => ({
  type: 'mouse',
  config: {
    eventType: 'mousemove',
    handler: (e) => handler({"mkMouseEvent": cb => cb["mkMouseEvent"](
      BigInt(e.clientX), BigInt(e.clientY), BigInt(e.pageX), BigInt(e.pageY), BigInt(e.button), BigInt(e.buttons)
    )})
  },
  now: [],
  get next() { return this; }
}) #-}

{-# COMPILE JS mousePosition = _ => handler => ({
  type: 'mouse',
  config: {
    eventType: 'mousemove',
    handler: (e) => handler(cases => cases['_,_'](BigInt(e.clientX), BigInt(e.clientY)))
  },
  now: [],
  get next() { return this; }
}) #-}

{-# COMPILE JS onMouseDown = _ => handler => ({
  type: 'mouse',
  config: {
    eventType: 'mousedown',
    handler: (e) => handler({"mkMouseEvent": cb => cb["mkMouseEvent"](
      BigInt(e.clientX), BigInt(e.clientY), BigInt(e.pageX), BigInt(e.pageY), BigInt(e.button), BigInt(e.buttons)
    )})
  },
  now: [],
  get next() { return this; }
}) #-}

{-# COMPILE JS onMouseUp = _ => handler => ({
  type: 'mouse',
  config: {
    eventType: 'mouseup',
    handler: (e) => handler({"mkMouseEvent": cb => cb["mkMouseEvent"](
      BigInt(e.clientX), BigInt(e.clientY), BigInt(e.pageX), BigInt(e.pageY), BigInt(e.button), BigInt(e.buttons)
    )})
  },
  now: [],
  get next() { return this; }
}) #-}

{-# COMPILE JS onGlobalClick = _ => handler => ({
  type: 'mouse',
  config: {
    eventType: 'click',
    handler: (e) => handler({"mkMouseEvent": cb => cb["mkMouseEvent"](
      BigInt(e.clientX), BigInt(e.clientY), BigInt(e.pageX), BigInt(e.pageY), BigInt(e.button), BigInt(e.buttons)
    )})
  },
  now: [],
  get next() { return this; }
}) #-}

------------------------------------------------------------------------
-- Utilities
------------------------------------------------------------------------

-- Left click only (button 0)
onLeftClick : ∀ {A : Set} → A → Event A
onLeftClick msg = mapFilterE (λ e → if button e ≡ᵇ 0 then just msg else nothing) (onMouseDown id)
  where
    open import Data.Nat using (_≡ᵇ_)
    open import Data.Maybe using (just; nothing)
    open import Function using (id)

-- Right click only (button 2)
onRightClick : ∀ {A : Set} → A → Event A
onRightClick msg = mapFilterE (λ e → if button e ≡ᵇ 2 then just msg else nothing) (onMouseDown id)
  where
    open import Data.Nat using (_≡ᵇ_)
    open import Data.Maybe using (just; nothing)
    open import Function using (id)
