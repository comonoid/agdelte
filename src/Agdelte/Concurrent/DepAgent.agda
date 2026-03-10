{-# OPTIONS --without-K --guardedness #-}

-- Research §2: Dependent Polynomials (DepAgent)
--
-- Full polynomial coalgebra: p(y) = Σ(o : O) y^{I(o)}
-- Input type depends on current observation.
--
-- Current Agent S I O has fixed fibers: I doesn't depend on O.
-- DepAgent allows: when state is (inj₁ s₁), input is I₁ not I₁ ⊎ I₂.
--
-- This gives exact type safety for ⊕ (internal choice) and
-- dependent protocols where available commands depend on state.

module Agdelte.Concurrent.DepAgent where

open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (id; const; _∘_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Agdelte.Concurrent.Agent as Fixed using (Agent; mkAgent)

------------------------------------------------------------------------
-- DepAgent: dependent polynomial coalgebra
------------------------------------------------------------------------

-- Full polynomial: p(y) = Σ(o : O) y^{I(o)}
-- The input fiber I depends on the current observation o.
record DepAgent (S : Set) (O : Set) (I : O → Set) : Set where
  field
    state   : S
    observe : S → O
    step    : (s : S) → I (observe s) → S

open DepAgent public

------------------------------------------------------------------------
-- Embedding: Agent ↪ DepAgent
------------------------------------------------------------------------

-- Every fixed-fiber Agent is a DepAgent with constant fiber.
embed : ∀ {S I O} → Agent S I O → DepAgent S O (const I)
embed a = record
  { state   = Fixed.state a
  ; observe = Fixed.observe a
  ; step    = Fixed.step a
  }

------------------------------------------------------------------------
-- Forgetful: DepAgent → Agent (flatten to Σ-type input)
------------------------------------------------------------------------

-- Forget the dependency: input becomes Σ O I (tagged input).
-- Requires decidable equality on O to check that the provided tag
-- matches the current observation before stepping.
forget : ∀ {S O I} → ((x y : O) → Dec (x ≡ y)) → DepAgent S O I → Agent S (Σ O I) O
forget dec da = mkAgent
  (state da)
  (observe da)
  (λ s oi → stepChecked dec da s oi)
  where
    stepChecked : ∀ {S O I} → ((x y : O) → Dec (x ≡ y)) → DepAgent S O I → S → Σ O I → S
    stepChecked dec da s (o , i) with dec o (observe da s)
    ... | yes refl = step da s i
    ... | no _     = s

------------------------------------------------------------------------
-- DepAgent step (returns new agent + output)
------------------------------------------------------------------------

-- Step a DepAgent: input type depends on current observation.
-- The caller must provide an input matching I (observe da (state da)).
stepDep : ∀ {S O I} → (da : DepAgent S O I) → I (observe da (state da)) → DepAgent S O I × O
stepDep da i =
  let s' = step da (state da) i
      da' = record da { state = s' }
  in da' , observe da s'

------------------------------------------------------------------------
-- Exact ⊕ for DepAgent
------------------------------------------------------------------------

-- Input fiber depends on which branch is active.
-- When state is inj₁ s₁, input is I₁ (not I₁ ⊎ I₂).
-- When state is inj₂ s₂, input is I₂.
-- No mismatched-tag no-op needed!

depI : ∀ {O₁ O₂ : Set} → (O₁ → Set) → (O₂ → Set) → O₁ ⊎ O₂ → Set
depI I₁ I₂ (inj₁ o₁) = I₁ o₁
depI I₁ I₂ (inj₂ o₂) = I₂ o₂

dep⊕ : ∀ {S₁ S₂ O₁ O₂}
       {I₁ : O₁ → Set} {I₂ : O₂ → Set}
     → DepAgent S₁ O₁ I₁
     → DepAgent S₂ O₂ I₂
     → DepAgent (S₁ ⊎ S₂) (O₁ ⊎ O₂) (depI I₁ I₂)
dep⊕ da₁ da₂ = record
  { state   = inj₁ (state da₁)
  ; observe = obsF
  ; step    = stepF
  }
  where
    obsF : _ → _
    obsF (inj₁ s₁) = inj₁ (observe da₁ s₁)
    obsF (inj₂ s₂) = inj₂ (observe da₂ s₂)

    stepF : (s : _) → _ → _
    stepF (inj₁ s₁) i = inj₁ (step da₁ s₁ i)
    stepF (inj₂ s₂) i = inj₂ (step da₂ s₂ i)

------------------------------------------------------------------------
-- Exact & for DepAgent
------------------------------------------------------------------------

-- External choice: both observable, input goes to one based on fiber.
dep& : ∀ {S₁ S₂ O₁ O₂}
       {I₁ : O₁ → Set} {I₂ : O₂ → Set}
     → DepAgent S₁ O₁ I₁
     → DepAgent S₂ O₂ I₂
     → DepAgent (S₁ × S₂) (O₁ × O₂) (λ { (o₁ , o₂) → I₁ o₁ ⊎ I₂ o₂ })
dep& da₁ da₂ = record
  { state   = state da₁ , state da₂
  ; observe = λ { (s₁ , s₂) → observe da₁ s₁ , observe da₂ s₂ }
  ; step    = λ { (s₁ , s₂) (inj₁ i₁) → step da₁ s₁ i₁ , s₂
                ; (s₁ , s₂) (inj₂ i₂) → s₁ , step da₂ s₂ i₂ }
  }

------------------------------------------------------------------------
-- Map output (covariant)
------------------------------------------------------------------------

-- NOTE: Unlike fixed-fiber Agent, you can't map output of a DepAgent
-- with just (f : O → O') because the input fiber I depends on O.
-- You need both directions: an isomorphism or a DepAgentLens.
-- Use throughDep below for the general case.

------------------------------------------------------------------------
-- DepAgentLens: morphism between dependent polynomials
------------------------------------------------------------------------

record DepAgentLens {O₁ O₂ : Set} (I₁ : O₁ → Set) (I₂ : O₂ → Set) : Set where
  field
    fwd : O₁ → O₂
    bwd : (o₁ : O₁) → I₂ (fwd o₁) → I₁ o₁

open DepAgentLens public

-- Apply dependent lens to DepAgent
throughDep : ∀ {S O₁ O₂ I₁ I₂} →
             DepAgentLens I₁ I₂ →
             DepAgent S O₁ I₁ →
             DepAgent S O₂ I₂
throughDep φ da = record
  { state   = state da
  ; observe = fwd φ ∘ observe da
  ; step    = λ s i₂ → step da s (bwd φ (observe da s) i₂)
  }
