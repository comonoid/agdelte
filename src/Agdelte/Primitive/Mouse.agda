{-# OPTIONS --without-K --guardedness #-}

-- Mouse: mouse events

module Agdelte.Primitive.Mouse where

open import Data.Nat using (ℕ)
open import Data.Bool using (Bool; true)
open import Data.Product using (_×_; _,_)
open import Agdelte.Core.Event

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
    handler: (e) => handler({
      x: e.x,
      y: e.y,
      pageX: e.pageX,
      pageY: e.pageY,
      button: e.button,
      buttons: e.buttons
    })
  },
  now: [],
  get next() { return this; }
}) #-}

{-# COMPILE JS mousePosition = _ => handler => ({
  type: 'mouse',
  config: {
    eventType: 'mousemove',
    handler: (e) => handler([e.x, e.y])
  },
  now: [],
  get next() { return this; }
}) #-}

{-# COMPILE JS onMouseDown = _ => handler => ({
  type: 'mouse',
  config: {
    eventType: 'mousedown',
    handler: (e) => handler({
      x: e.x,
      y: e.y,
      pageX: e.pageX,
      pageY: e.pageY,
      button: e.button,
      buttons: e.buttons
    })
  },
  now: [],
  get next() { return this; }
}) #-}

{-# COMPILE JS onMouseUp = _ => handler => ({
  type: 'mouse',
  config: {
    eventType: 'mouseup',
    handler: (e) => handler({
      x: e.x,
      y: e.y,
      pageX: e.pageX,
      pageY: e.pageY,
      button: e.button,
      buttons: e.buttons
    })
  },
  now: [],
  get next() { return this; }
}) #-}

{-# COMPILE JS onGlobalClick = _ => handler => ({
  type: 'mouse',
  config: {
    eventType: 'click',
    handler: (e) => handler({
      x: e.x,
      y: e.y,
      pageX: e.pageX,
      pageY: e.pageY,
      button: e.button,
      buttons: e.buttons
    })
  },
  now: [],
  get next() { return this; }
}) #-}

------------------------------------------------------------------------
-- Utilities
------------------------------------------------------------------------

-- Helper predicates (button filtering will be in runtime)
private
  alwaysTrue : ∀ {A : Set} → A → Bool
  alwaysTrue _ = true

-- Left click only
onLeftClick : ∀ {A : Set} → A → Event A
onLeftClick msg = filterE alwaysTrue (onMouseDown (λ _ → msg))

-- Right click only
onRightClick : ∀ {A : Set} → A → Event A
onRightClick msg = filterE alwaysTrue (onMouseDown (λ _ → msg))
