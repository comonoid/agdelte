{-# OPTIONS --without-K --guardedness #-}

-- Keyboard: события клавиатуры

module Agdelte.Primitive.Keyboard where

open import Data.String using (String)
open import Data.Bool using (Bool)
open import Data.Product using (_×_)
open import Agdelte.Core.Event

------------------------------------------------------------------------
-- Keyboard Event Data
------------------------------------------------------------------------

record KeyEvent : Set where
  constructor mkKeyEvent
  field
    key   : String    -- "a", "Enter", "ArrowUp", etc.
    code  : String    -- "KeyA", "Enter", "ArrowUp"
    ctrl  : Bool
    alt   : Bool
    shift : Bool
    meta  : Bool      -- Cmd на Mac, Win на Windows

open KeyEvent public

------------------------------------------------------------------------
-- Keyboard Events
------------------------------------------------------------------------

postulate
  -- Подписка на нажатие клавиш
  onKeyDown : ∀ {A : Set} → (KeyEvent → A) → Event A

  -- Подписка на отпускание клавиш
  onKeyUp : ∀ {A : Set} → (KeyEvent → A) → Event A

  -- Подписка на конкретную клавишу
  onKey : ∀ {A : Set} → String → A → Event A

  -- Подписка на стрелки (возвращает событие когда нажата любая стрелка)
  onArrowKeys : ∀ {A : Set} → A → A → A → A → Event A  -- up, down, left, right

  -- Подписка на стрелки + Escape
  onArrowKeysWithEscape : ∀ {A : Set} → A → A → A → A → A → Event A  -- up, down, left, right, escape

{-# COMPILE JS onKeyDown = _ => handler => ({
  type: 'keyboard',
  config: {
    eventType: 'keydown',
    handler: (e) => handler({
      key: e.key,
      code: e.code,
      ctrl: e.ctrl,
      alt: e.alt,
      shift: e.shift,
      meta: e.meta
    })
  },
  now: [],
  get next() { return this; }
}) #-}

{-# COMPILE JS onKeyUp = _ => handler => ({
  type: 'keyboard',
  config: {
    eventType: 'keyup',
    handler: (e) => handler({
      key: e.key,
      code: e.code,
      ctrl: e.ctrl,
      alt: e.alt,
      shift: e.shift,
      meta: e.meta
    })
  },
  now: [],
  get next() { return this; }
}) #-}

{-# COMPILE JS onKey = _ => key => msg => ({
  type: 'keyboard',
  config: {
    eventType: 'keydown',
    handler: (e) => e.key === key ? msg : null
  },
  now: [],
  get next() { return this; }
}) #-}

{-# COMPILE JS onArrowKeys = _ => up => down => left => right => ({
  type: 'keyboard',
  config: {
    eventType: 'keydown',
    handler: (e) => {
      switch (e.key) {
        case 'ArrowUp': return up;
        case 'ArrowDown': return down;
        case 'ArrowLeft': return left;
        case 'ArrowRight': return right;
        default: return null;
      }
    }
  },
  now: [],
  get next() { return this; }
}) #-}

{-# COMPILE JS onArrowKeysWithEscape = _ => up => down => left => right => esc => ({
  type: 'keyboard',
  config: {
    eventType: 'keydown',
    handler: (e) => {
      switch (e.key) {
        case 'ArrowUp': return up;
        case 'ArrowDown': return down;
        case 'ArrowLeft': return left;
        case 'ArrowRight': return right;
        case 'Escape': return esc;
        default: return null;
      }
    }
  },
  now: [],
  get next() { return this; }
}) #-}

------------------------------------------------------------------------
-- Удобные обёртки
------------------------------------------------------------------------

-- Стрелки
onArrowUp : ∀ {A : Set} → A → Event A
onArrowUp = onKey "ArrowUp"

onArrowDown : ∀ {A : Set} → A → Event A
onArrowDown = onKey "ArrowDown"

onArrowLeft : ∀ {A : Set} → A → Event A
onArrowLeft = onKey "ArrowLeft"

onArrowRight : ∀ {A : Set} → A → Event A
onArrowRight = onKey "ArrowRight"

-- Специальные клавиши
onEnter : ∀ {A : Set} → A → Event A
onEnter = onKey "Enter"

onEscape : ∀ {A : Set} → A → Event A
onEscape = onKey "Escape"

onSpace : ∀ {A : Set} → A → Event A
onSpace = onKey " "

onTab : ∀ {A : Set} → A → Event A
onTab = onKey "Tab"

onBackspace : ∀ {A : Set} → A → Event A
onBackspace = onKey "Backspace"

onDelete : ∀ {A : Set} → A → Event A
onDelete = onKey "Delete"

-- WASD для игр
onW : ∀ {A : Set} → A → Event A
onW = onKey "w"

onA : ∀ {A : Set} → A → Event A
onA = onKey "a"

onS : ∀ {A : Set} → A → Event A
onS = onKey "s"

onD : ∀ {A : Set} → A → Event A
onD = onKey "d"
