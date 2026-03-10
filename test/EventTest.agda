{-# OPTIONS --without-K #-}

-- EventTest: tests for Event combinators using SimEvent (list-based testing)
-- All tests are propositional equality proofs checked at type-check time.

module EventTest where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Agdelte.Test.Interpret as TI
open TI using (SimEvent; simMapE; simFilterE; simMerge; simFoldE; simAccumE; simMapFilterE; interpretApp)

------------------------------------------------------------------------
-- Basic tests
------------------------------------------------------------------------

-- mapE over events
test-mapE : simMapE suc ((1 ∷ 2 ∷ []) ∷ (3 ∷ []) ∷ [])
          ≡ ((2 ∷ 3 ∷ []) ∷ (4 ∷ []) ∷ [])
test-mapE = refl

-- filterE removes non-matching events
isPositive : ℕ → Bool
isPositive zero    = false
isPositive (suc _) = true

test-filterE : simFilterE isPositive ((0 ∷ 1 ∷ 2 ∷ []) ∷ (3 ∷ 0 ∷ []) ∷ [])
             ≡ ((1 ∷ 2 ∷ []) ∷ (3 ∷ []) ∷ [])
test-filterE = refl

------------------------------------------------------------------------
-- Merge tests
------------------------------------------------------------------------

-- merge combines events at matching ticks
test-merge : simMerge ((1 ∷ []) ∷ [] ∷ [])
                      ((10 ∷ []) ∷ (20 ∷ []) ∷ [])
           ≡ ((1 ∷ 10 ∷ []) ∷ (20 ∷ []) ∷ [])
test-merge = refl

-- merge with empty
test-merge-empty : simMerge {ℕ} [] ((1 ∷ []) ∷ [])
                 ≡ ((1 ∷ []) ∷ [])
test-merge-empty = refl

------------------------------------------------------------------------
-- Fold tests
------------------------------------------------------------------------

-- foldE accumulates (count events)
test-foldE : simFoldE 0 (λ _ n → suc n)
              ((1 ∷ []) ∷ (2 ∷ 3 ∷ []) ∷ [] ∷ (4 ∷ []) ∷ [])
           ≡ ((1 ∷ []) ∷ (2 ∷ 3 ∷ []) ∷ [] ∷ (4 ∷ []) ∷ [])
test-foldE = refl

-- foldE with sum accumulation
test-foldE-sum : simFoldE 0 _+_
                  ((1 ∷ []) ∷ (2 ∷ 3 ∷ []) ∷ [])
               ≡ ((1 ∷ []) ∷ (3 ∷ 6 ∷ []) ∷ [])
test-foldE-sum = refl

------------------------------------------------------------------------
-- AccumE tests
------------------------------------------------------------------------

-- accumE applies function events to accumulator
test-accumE : simAccumE 0 ((suc ∷ []) ∷ (suc ∷ suc ∷ []) ∷ [])
            ≡ ((1 ∷ []) ∷ (2 ∷ 3 ∷ []) ∷ [])
test-accumE = refl

------------------------------------------------------------------------
-- MapFilterE tests
------------------------------------------------------------------------

-- mapFilterE filters via Maybe
doublePositive : ℕ → Maybe ℕ
doublePositive zero    = nothing
doublePositive (suc n) = just (suc n + suc n)

test-mapFilterE : simMapFilterE doublePositive
                    ((0 ∷ 1 ∷ 2 ∷ []) ∷ (0 ∷ 3 ∷ []) ∷ [])
                ≡ ((2 ∷ 4 ∷ []) ∷ (6 ∷ []) ∷ [])
test-mapFilterE = refl

------------------------------------------------------------------------
-- InterpretApp tests
------------------------------------------------------------------------

-- Test reactive app: counter that increments on each message
test-app : interpretApp (λ _ n → suc n) 0
            ((1 ∷ []) ∷ (2 ∷ 3 ∷ []) ∷ [] ∷ [])
         ≡ (1 ∷ 3 ∷ 3 ∷ [])
test-app = refl

------------------------------------------------------------------------
-- All tests pass if this module compiles!
------------------------------------------------------------------------

allTestsPassed : Bool
allTestsPassed = true
