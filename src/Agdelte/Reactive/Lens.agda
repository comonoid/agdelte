{-# OPTIONS --without-K #-}

-- Practical Lens for Widget composition
-- Unlike Theory/Poly.agda (abstract polynomial lenses),
-- these are concrete get/set lenses for model navigation.

module Agdelte.Reactive.Lens where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (_∘_; id)

------------------------------------------------------------------------
-- Lens: get/set pair with laws (not proven here, see Phase 9)
------------------------------------------------------------------------

record Lens (Outer Inner : Set) : Set where
  constructor mkLens
  field
    get : Outer → Inner
    set : Inner → Outer → Outer

  -- Derived: modify inner value
  modify : (Inner → Inner) → Outer → Outer
  modify f outer = set (f (get outer)) outer

open Lens public

------------------------------------------------------------------------
-- Identity and Composition
------------------------------------------------------------------------

-- Identity lens
idLens : ∀ {A} → Lens A A
idLens = mkLens id (λ a _ → a)

-- Lens composition: zoom deeper
_∘L_ : ∀ {A B C} → Lens B C → Lens A B → Lens A C
inner ∘L outer = mkLens
  (get inner ∘ get outer)
  (λ c a → set outer (set inner c (get outer a)) a)

------------------------------------------------------------------------
-- Product lenses (for composed models)
------------------------------------------------------------------------

-- Focus on first component of a pair
fstLens : ∀ {A B} → Lens (A × B) A
fstLens = mkLens proj₁ (λ a (_ , b) → a , b)

-- Focus on second component of a pair
sndLens : ∀ {A B} → Lens (A × B) B
sndLens = mkLens proj₂ (λ b (a , _) → a , b)
