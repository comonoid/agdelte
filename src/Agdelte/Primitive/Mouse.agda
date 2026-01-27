{-# OPTIONS --without-K --guardedness #-}

-- Mouse: события мыши

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

-- Позиция мыши
Position : Set
Position = ℕ × ℕ

------------------------------------------------------------------------
-- Mouse Events
------------------------------------------------------------------------

postulate
  -- Движение мыши
  onMouseMove : ∀ {A : Set} → (MouseEvent → A) → Event A

  -- Позиция мыши (упрощённо)
  mousePosition : ∀ {A : Set} → (Position → A) → Event A

  -- Клики
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
-- Утилиты
------------------------------------------------------------------------

-- Вспомогательные предикаты (фильтрация по button будет в runtime)
private
  alwaysTrue : ∀ {A : Set} → A → Bool
  alwaysTrue _ = true

-- Только левый клик
onLeftClick : ∀ {A : Set} → A → Event A
onLeftClick msg = filterE alwaysTrue (onMouseDown (λ _ → msg))

-- Только правый клик
onRightClick : ∀ {A : Set} → A → Event A
onRightClick msg = filterE alwaysTrue (onMouseDown (λ _ → msg))
