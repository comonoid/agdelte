{-# OPTIONS --without-K --guardedness #-}

-- Proof: dual is an involution on Session types
-- dual (dual s) ≡ s for all s : Session

module Agdelte.Theory.SessionDualProof where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)

open import Agdelte.Concurrent.Session

------------------------------------------------------------------------
-- dual (dual s) ≡ s
------------------------------------------------------------------------

dual-involution : (s : Session) → dual (dual s) ≡ s
dual-involution (send A s)     = cong (send A) (dual-involution s)
dual-involution (recv A s)     = cong (recv A) (dual-involution s)
dual-involution (offer s₁ s₂)  = cong₂ offer (dual-involution s₁) (dual-involution s₂)
dual-involution (choose s₁ s₂) = cong₂ choose (dual-involution s₁) (dual-involution s₂)
dual-involution done            = refl

------------------------------------------------------------------------
-- Corollary: dual is injective
------------------------------------------------------------------------

-- dual s₁ ≡ dual s₂ → s₁ ≡ s₂
-- Proof: s₁ ≡ dual(dual s₁) ≡ dual(dual s₂) ≡ s₂
dual-injective : ∀ {s₁ s₂ : Session} → dual s₁ ≡ dual s₂ → s₁ ≡ s₂
dual-injective {s₁} {s₂} p =
  trans (sym (dual-involution s₁))
        (trans (cong dual p) (dual-involution s₂))

------------------------------------------------------------------------
-- SessionI and SessionO respect duality
------------------------------------------------------------------------

open import Data.Product using (_×_)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤)

-- SessionI (dual s) ≡ SessionO s:
--   dual swaps send↔recv, offer↔choose
--   SessionI(choose) = × and SessionO(offer) = ×
--   SessionI(offer) = ⊎ and SessionO(choose) = ⊎
dual-IO : (s : Session) → SessionI (dual s) ≡ SessionO s
dual-IO (send A s)     = cong (A ×_) (dual-IO s)
dual-IO (recv A s)     = dual-IO s
dual-IO (offer s₁ s₂)  = cong₂ _×_ (dual-IO s₁) (dual-IO s₂)
dual-IO (choose s₁ s₂) = cong₂ _⊎_ (dual-IO s₁) (dual-IO s₂)
dual-IO done            = refl

-- Symmetric: SessionO (dual s) ≡ SessionI s
dual-OI : (s : Session) → SessionO (dual s) ≡ SessionI s
dual-OI (send A s)     = dual-OI s
dual-OI (recv A s)     = cong (A ×_) (dual-OI s)
dual-OI (offer s₁ s₂)  = cong₂ _⊎_ (dual-OI s₁) (dual-OI s₂)
dual-OI (choose s₁ s₂) = cong₂ _×_ (dual-OI s₁) (dual-OI s₂)
dual-OI done            = refl
