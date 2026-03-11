{-# OPTIONS --without-K --guardedness #-}

-- Wiring.Debug: debug-only agent combinator with crash on mismatch
--
-- WARNING: This module is --unsafe. debugTrap inhabits every type.
-- Use _⊕!_ during development to detect routing bugs.
-- Replace with _⊕_ (from Wiring) for production.
--
-- Separated from Wiring to keep the core module logically safe.

module Agdelte.Concurrent.Wiring.Debug where

open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String)

open import Agdelte.Concurrent.Agent
open import Agdelte.Concurrent.Wiring using (SomeAgent; someAgent)

private
  variable
    S₁ S₂ I₁ I₂ O₁ O₂ : Set

------------------------------------------------------------------------
-- debugTrap: inhabits every type (throws at runtime)
------------------------------------------------------------------------

postulate
  debugTrap : ∀ {A : Set} → String → A

{-# COMPILE JS debugTrap = function(msg) {
  throw new Error("⊕! mismatch: " + msg);
} #-}

------------------------------------------------------------------------
-- ⊕! : coproduct agent with crash on mismatched state/input tags
------------------------------------------------------------------------

infixr 5 _⊕!_
_⊕!_ : Agent S₁ I₁ O₁ → Agent S₂ I₂ O₂ → Agent (S₁ ⊎ S₂) (I₁ ⊎ I₂) (O₁ ⊎ O₂)
a ⊕! b = record
  { state   = inj₁ (state a)
  ; observe = λ { (inj₁ s₁) → inj₁ (observe a s₁)
                ; (inj₂ s₂) → inj₂ (observe b s₂) }
  ; step    = λ { (inj₁ s₁) (inj₁ i₁) → inj₁ (step a s₁ i₁)
                ; (inj₂ s₂) (inj₂ i₂) → inj₂ (step b s₂ i₂)
                ; (inj₁ _)  (inj₂ _)   → debugTrap "left state, right input"
                ; (inj₂ _)  (inj₁ _)   → debugTrap "right state, left input" }
  }

-- Packed version
_⊕!ₛ_ : SomeAgent I₁ O₁ → SomeAgent I₂ O₂ → SomeAgent (I₁ ⊎ I₂) (O₁ ⊎ O₂)
someAgent a ⊕!ₛ someAgent b = someAgent (a ⊕! b)
