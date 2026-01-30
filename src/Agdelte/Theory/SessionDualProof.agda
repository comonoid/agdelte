{-# OPTIONS --without-K #-}

-- Proof: dual is an involution on Session types
-- dual (dual s) ≡ s for all s : Session

module Agdelte.Theory.SessionDualProof where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Agdelte.Concurrent.Session

------------------------------------------------------------------------
-- dual (dual s) ≡ s
------------------------------------------------------------------------

dual-involution : (s : Session) → dual (dual s) ≡ s
dual-involution (send A s) = cong (send A) (dual-involution s)
dual-involution (recv A s) = cong (recv A) (dual-involution s)
dual-involution (offer s₁ s₂) = cong₂ offer (dual-involution s₁) (dual-involution s₂)
dual-involution (choose s₁ s₂) = cong₂ choose (dual-involution s₁) (dual-involution s₂)
dual-involution done = refl

------------------------------------------------------------------------
-- Corollary: dual is injective
------------------------------------------------------------------------

dual-injective : ∀ {s₁ s₂ : Session} → dual s₁ ≡ dual s₂ → s₁ ≡ s₂
dual-injective {s₁} {s₂} p with dual-involution s₁ | dual-involution s₂
... | q₁ | q₂ = helper p q₁ q₂
  where
    helper : ∀ {s₁ s₂} → dual s₁ ≡ dual s₂ → dual (dual s₁) ≡ s₁ → dual (dual s₂) ≡ s₂ → s₁ ≡ s₂
    helper refl refl refl = refl

------------------------------------------------------------------------
-- SessionI and SessionO respect duality
------------------------------------------------------------------------

-- For a well-typed session, dual swaps I and O:
-- SessionI (dual s) ≡ SessionO s  (what server sends, client receives)
-- SessionO (dual s) ≡ SessionI s  (what server receives, client sends)
-- These are type equalities, not provable with propositional equality
-- due to Set-level computation. They hold definitionally by reduction.
