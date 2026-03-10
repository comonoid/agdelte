{-# OPTIONS --without-K --guardedness #-}

-- Keyboard: keyboard events (thin wrapper over Core.Event)
--
-- For the canonical API, use Core.Event constructors directly.
-- This module provides a simpler interface where handlers always
-- produce a value (no Maybe filtering), plus convenience wrappers.

module Agdelte.Primitive.Keyboard where

open import Data.Nat using (ℕ)
open import Data.String using (String)
open import Data.Bool using (Bool)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_)
open import Data.List using (List)

open import Agdelte.Core.Event public
  using ( Event; KeyboardEvent; mkKeyboardEvent
        ; key; code; ctrl; alt; shift; meta; repeat; location
        )

import Agdelte.Core.Event as CE

------------------------------------------------------------------------
-- Backward compatibility alias
------------------------------------------------------------------------

KeyEvent : Set
KeyEvent = KeyboardEvent

------------------------------------------------------------------------
-- Keyboard Events (always-producing wrappers)
-- Named with "All" suffix to distinguish from Core.Event's Maybe-based
-- variants (onKeyDown, onKeyUp) when both modules are in scope.
------------------------------------------------------------------------

-- Subscribe to all key presses (no filtering)
onKeyDownAll : ∀ {A : Set} → (KeyEvent → A) → Event A
onKeyDownAll f = CE.onKeyDown (λ e → just (f e))

-- Subscribe to all key releases (no filtering)
onKeyUpAll : ∀ {A : Set} → (KeyEvent → A) → Event A
onKeyUpAll f = CE.onKeyUp (λ e → just (f e))

-- Subscribe to specific key
onKey : ∀ {A : Set} → String → A → Event A
onKey = CE.onKey

-- Subscribe to arrow keys (returns event when any arrow is pressed)
onArrowKeys : ∀ {A : Set} → A → A → A → A → Event A  -- up, down, left, right
onArrowKeys up down left right =
  CE.onKeys (("ArrowUp" , up) ∷ ("ArrowDown" , down) ∷ ("ArrowLeft" , left) ∷ ("ArrowRight" , right) ∷ [])
  where open import Data.List using (_∷_; [])

-- Subscribe to arrow keys + Escape
onArrowKeysWithEscape : ∀ {A : Set} → A → A → A → A → A → Event A
onArrowKeysWithEscape up down left right esc =
  CE.onKeys (("ArrowUp" , up) ∷ ("ArrowDown" , down) ∷ ("ArrowLeft" , left) ∷ ("ArrowRight" , right) ∷ ("Escape" , esc) ∷ [])
  where open import Data.List using (_∷_; [])

------------------------------------------------------------------------
-- Convenient wrappers (re-exported from Core.Event)
------------------------------------------------------------------------

-- Arrows
onArrowUp : ∀ {A : Set} → A → Event A
onArrowUp = CE.onArrowUp

onArrowDown : ∀ {A : Set} → A → Event A
onArrowDown = CE.onArrowDown

onArrowLeft : ∀ {A : Set} → A → Event A
onArrowLeft = CE.onArrowLeft

onArrowRight : ∀ {A : Set} → A → Event A
onArrowRight = CE.onArrowRight

-- Special keys
onEnter : ∀ {A : Set} → A → Event A
onEnter = CE.onEnter

onEscape : ∀ {A : Set} → A → Event A
onEscape = CE.onEscape

onSpace : ∀ {A : Set} → A → Event A
onSpace = CE.onSpace

onTab : ∀ {A : Set} → A → Event A
onTab = onKey "Tab"

onBackspace : ∀ {A : Set} → A → Event A
onBackspace = onKey "Backspace"

onDelete : ∀ {A : Set} → A → Event A
onDelete = onKey "Delete"

-- WASD for games
onW : ∀ {A : Set} → A → Event A
onW = onKey "w"

onA : ∀ {A : Set} → A → Event A
onA = onKey "a"

onS : ∀ {A : Set} → A → Event A
onS = onKey "s"

onD : ∀ {A : Set} → A → Event A
onD = onKey "d"
