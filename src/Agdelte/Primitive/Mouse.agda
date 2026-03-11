{-# OPTIONS --without-K --guardedness #-}

-- Mouse: mouse events (thin wrapper over Core.Event)
--
-- For the canonical API, use Core.Event constructors directly.
-- This module provides a simpler interface where handlers always
-- produce a value (no Maybe filtering).

module Agdelte.Primitive.Mouse where

open import Data.Bool using (if_then_else_)
open import Data.Nat using (ℕ; _≡ᵇ_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_)

open import Agdelte.Core.Event public
  using ( Event; MouseEvent; mkMouseEvent
        ; mouseX; mouseY; pageX; pageY; button; buttons
        ; mapFilterE
        )

import Agdelte.Core.Event as CE

------------------------------------------------------------------------
-- Mouse position
------------------------------------------------------------------------

Position : Set
Position = ℕ × ℕ

------------------------------------------------------------------------
-- Mouse Events (always-producing wrappers)
-- Named with "All" suffix to distinguish from Core.Event's Maybe-based
-- variants when both modules are in scope.
------------------------------------------------------------------------

-- All mouse movement (no filtering)
onMouseMoveAll : ∀ {A : Set} → (MouseEvent → A) → Event A
onMouseMoveAll f = CE.onMouseMove (λ e → just (f e))

-- Mouse position (simplified)
mousePosition : ∀ {A : Set} → (Position → A) → Event A
mousePosition f = CE.onMouseMove (λ e → just (f (mouseX e , mouseY e)))

-- All clicks (no filtering)
onMouseDownAll : ∀ {A : Set} → (MouseEvent → A) → Event A
onMouseDownAll f = CE.onMouseDown (λ e → just (f e))

onMouseUpAll : ∀ {A : Set} → (MouseEvent → A) → Event A
onMouseUpAll f = CE.onMouseUp (λ e → just (f e))

onGlobalClickAll : ∀ {A : Set} → (MouseEvent → A) → Event A
onGlobalClickAll f = CE.onClick (λ e → just (f e))

------------------------------------------------------------------------
-- Utilities
------------------------------------------------------------------------

-- Left click only (button 0)
onLeftClick : ∀ {A : Set} → A → Event A
onLeftClick msg = CE.onClick (λ e → if button e ≡ᵇ 0 then just msg else nothing)

-- Right click only (button 2)
onRightClick : ∀ {A : Set} → A → Event A
onRightClick msg = CE.onClick (λ e → if button e ≡ᵇ 2 then just msg else nothing)
