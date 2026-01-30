{-# OPTIONS --without-K #-}

-- Lens laws proofs for practical lenses from Agdelte.Reactive.Lens
--
-- Three laws for a well-behaved lens:
--   get-set : get (set v s) ≡ v
--   set-get : set (get s) s ≡ s
--   set-set : set v₂ (set v₁ s) ≡ set v₂ s
--
-- Proven for: fstLens, sndLens, idLens

module Agdelte.Theory.LensLaws where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Agdelte.Reactive.Lens

------------------------------------------------------------------------
-- Law definitions
------------------------------------------------------------------------

record LensLawful {Outer Inner : Set} (l : Lens Outer Inner) : Set where
  private
    g = Lens.get l
    s = Lens.set l
  field
    get-set : ∀ (v : Inner) (o : Outer) → g (s v o) ≡ v
    set-get : ∀ (o : Outer) → s (g o) o ≡ o
    set-set : ∀ (v₁ v₂ : Inner) (o : Outer) → s v₂ (s v₁ o) ≡ s v₂ o

------------------------------------------------------------------------
-- idLens is lawful
------------------------------------------------------------------------

idLens-lawful : ∀ {A : Set} → LensLawful (idLens {A})
idLens-lawful = record
  { get-set = λ _ _ → refl
  ; set-get = λ _ → refl
  ; set-set = λ _ _ _ → refl
  }

------------------------------------------------------------------------
-- fstLens is lawful
------------------------------------------------------------------------

fstLens-lawful : ∀ {A B : Set} → LensLawful (fstLens {A} {B})
fstLens-lawful = record
  { get-set = λ _ _ → refl
  ; set-get = λ _ → refl
  ; set-set = λ _ _ _ → refl
  }

------------------------------------------------------------------------
-- sndLens is lawful
------------------------------------------------------------------------

sndLens-lawful : ∀ {A B : Set} → LensLawful (sndLens {A} {B})
sndLens-lawful = record
  { get-set = λ _ _ → refl
  ; set-get = λ _ → refl
  ; set-set = λ _ _ _ → refl
  }

------------------------------------------------------------------------
-- Composition preserves laws
------------------------------------------------------------------------

∘L-lawful : ∀ {A B C : Set}
          → (inner : Lens B C) → (outer : Lens A B)
          → LensLawful inner → LensLawful outer
          → LensLawful (inner ∘L outer)
∘L-lawful inner outer li lo = record
  { get-set = gs
  ; set-get = sg
  ; set-set = ss
  }
  where
    open Lens inner renaming (get to getI; set to setI)
    open Lens outer renaming (get to getO; set to setO)
    open LensLawful li renaming (get-set to gsI; set-get to sgI; set-set to ssI)
    open LensLawful lo renaming (get-set to gsO; set-get to sgO; set-set to ssO)

    open import Relation.Binary.PropositionalEquality using (cong; trans)

    gs : ∀ v s → getI (getO (setO (setI v (getO s)) s)) ≡ v
    gs v s = trans (cong getI (gsO (setI v (getO s)) s)) (gsI v (getO s))

    sg : ∀ s → setO (setI (getI (getO s)) (getO s)) s ≡ s
    sg s = trans (cong (λ b → setO b s) (sgI (getO s))) (sgO s)

    ss : ∀ v₁ v₂ s → setO (setI v₂ (getO (setO (setI v₁ (getO s)) s))) (setO (setI v₁ (getO s)) s) ≡ setO (setI v₂ (getO s)) s
    ss v₁ v₂ s =
      trans (cong (λ b → setO (setI v₂ b) (setO (setI v₁ (getO s)) s)) (gsO (setI v₁ (getO s)) s))
      (trans (cong (λ b → setO b (setO (setI v₁ (getO s)) s)) (ssI v₁ v₂ (getO s)))
             (ssO (setI v₁ (getO s)) (setI v₂ (getO s)) s))
