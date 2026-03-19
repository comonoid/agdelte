{-# OPTIONS --without-K #-}

-- Mouse convenience constructors for Event.
-- Re-exported by Agdelte.Core.Event for backward compatibility.

module Agdelte.Core.Event.Mouse where

open import Data.Bool using (if_then_else_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Float using (Float)

open import Agdelte.Core.Event.Core using
  ( Event; MouseEvent; mouseX; mouseY; button; onClick; onMouseMove
  )

private
  variable
    A : Set

Position : Set
Position = Float × Float

onLeftClick : A → Event A
onLeftClick msg = onClick (λ e → if button e ≡ᵇ 0 then just msg else nothing)
  where open import Data.Nat using (_≡ᵇ_)

onRightClick : A → Event A
onRightClick msg = onClick (λ e → if button e ≡ᵇ 2 then just msg else nothing)
  where open import Data.Nat using (_≡ᵇ_)

mousePosition : (Position → A) → Event A
mousePosition f = onMouseMove (λ e → just (f (mouseX e , mouseY e)))
