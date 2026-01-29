{-# OPTIONS --without-K --guardedness #-}

-- EventTest: tests for Event combinators

module EventTest where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Agdelte.Core.Signal
open import Agdelte.Core.Event

------------------------------------------------------------------------
-- Basic tests
------------------------------------------------------------------------

-- never does not generate events
test-never : ∀ {A : Set} → now (never {A}) ≡ []
test-never = refl

-- once generates one event
test-once : now (once 42) ≡ (42 ∷ [])
test-once = refl

-- mapE preserves structure
test-mapE : now (mapE suc (once 0)) ≡ (1 ∷ [])
test-mapE = refl

------------------------------------------------------------------------
-- Merge tests
------------------------------------------------------------------------

-- merge combines events
test-merge : now (merge (once 1) (once 2)) ≡ (1 ∷ 2 ∷ [])
test-merge = refl

-- merge with never
test-merge-never : now (merge (once 1) never) ≡ (1 ∷ [])
test-merge-never = refl

------------------------------------------------------------------------
-- Filter tests
------------------------------------------------------------------------

-- filterE
isEven : ℕ → Bool
isEven zero = true
isEven (suc zero) = false
isEven (suc (suc n)) = isEven n

test-filterE : now (filterE isEven (emit (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [])))
             ≡ (0 ∷ 2 ∷ 4 ∷ [])
test-filterE = refl

------------------------------------------------------------------------
-- Fold tests
------------------------------------------------------------------------

-- foldE accumulates
test-foldE-now : now (foldE _+_ 0 (emit (1 ∷ 2 ∷ 3 ∷ []))) ≡ 6
test-foldE-now = refl

-- count counts events
test-count : now (count (emit (1 ∷ 2 ∷ 3 ∷ []))) ≡ 3
test-count = refl

------------------------------------------------------------------------
-- Snapshot tests
------------------------------------------------------------------------

-- snapshot combines
test-snapshot : now (snapshot (once 1) (constant 10)) ≡ ((1 , 10) ∷ [])
test-snapshot = refl

------------------------------------------------------------------------
-- Gate tests
------------------------------------------------------------------------

-- gate passes when true
test-gate-true : now (gate (once 1) (constant true)) ≡ (1 ∷ [])
test-gate-true = refl

-- gate blocks when false
test-gate-false : now (gate (once 1) (constant false)) ≡ []
test-gate-false = refl

------------------------------------------------------------------------
-- Signal tests
------------------------------------------------------------------------

-- constant always returns the value
test-constant : now (constant 42) ≡ 42
test-constant = refl

-- mapS applies function
test-mapS : now (mapS suc (constant 0)) ≡ 1
test-mapS = refl

-- Applicative
test-applicative : now (pure suc <*> constant 0) ≡ 1
test-applicative = refl

-- pre delays
test-pre : now (pre 0 (constant 1)) ≡ 0
test-pre = refl

------------------------------------------------------------------------
-- All tests pass if this module compiles!
------------------------------------------------------------------------

allTestsPassed : Bool
allTestsPassed = true
