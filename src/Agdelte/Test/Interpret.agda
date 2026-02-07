{-# OPTIONS --without-K #-}

-- Pure testing framework for event combinators
-- No DOM, no browser — test transformations as pure functions on lists
--
-- Key idea: represent an event stream as List (List A)
--   outer list = ticks (discrete time steps)
--   inner list = simultaneous events within one tick
--
-- Why a separate SimEvent and not the real Event AST?
-- Event is an AST describing runtime subscriptions (interval, httpGet, etc).
-- It cannot be "run" purely — it needs a browser/runtime to fire events.
-- SimEvent is a concrete list of values, enabling propositional equality
-- proofs (test-mapE, test-foldE, etc.) that Agda checks at type-check time.
--
-- The combinators here (simMapE, simFoldE, ...) mirror the real ones
-- (mapE, foldE, ...) on a pure data structure, so we can verify the
-- transformation logic without side effects.

module Agdelte.Test.Interpret where

open import Data.List using (List; []; _∷_; map; concat; concatMap; length; _++_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private
  variable
    A B C S : Set

------------------------------------------------------------------------
-- SimEvent: list-based event stream for testing
------------------------------------------------------------------------

-- Each element is one tick; each tick has zero or more simultaneous events
SimEvent : Set → Set
SimEvent A = List (List A)

------------------------------------------------------------------------
-- Combinators on SimEvent (pure, testable)
------------------------------------------------------------------------

-- Map over all events
simMapE : (A → B) → SimEvent A → SimEvent B
simMapE f = map (map f)

-- Filter events
simFilterE : (A → Bool) → SimEvent A → SimEvent A
simFilterE p = map (filterList p)
  where
    filterList : (A → Bool) → List A → List A
    filterList p [] = []
    filterList p (x ∷ xs) = if p x then x ∷ filterList p xs else filterList p xs

-- Map + filter via Maybe
simMapFilterE : (A → Maybe B) → SimEvent A → SimEvent B
simMapFilterE f = map (collectJust f)
  where
    collectJust : (A → Maybe B) → List A → List B
    collectJust f [] = []
    collectJust f (x ∷ xs) with f x
    ... | just y  = y ∷ collectJust f xs
    ... | nothing = collectJust f xs

-- Merge two event streams (zip by tick, concatenate within tick)
simMerge : SimEvent A → SimEvent A → SimEvent A
simMerge [] ys = ys
simMerge xs [] = xs
simMerge (x ∷ xs) (y ∷ ys) = (x ++ y) ∷ simMerge xs ys

-- Fold: accumulate state across ticks
-- On each event in tick, update accumulator and emit it
simFoldE : A → (B → A → A) → SimEvent B → SimEvent A
simFoldE {A} {B} _   step [] = []
simFoldE {A} {B} acc step (tick ∷ rest) = emitted ∷ simFoldE acc' step rest
  where
    foldTick : A → List B → List A × A
    foldTick a [] = ([] , a)
    foldTick a (b ∷ bs) =
      let a' = step b a in
      let (emits , final) = foldTick a' bs
      in (a' ∷ emits , final)
    result = foldTick acc tick
    emitted = proj₁ result
    acc' = proj₂ result

-- AccumE: apply function events to accumulator
simAccumE : A → SimEvent (A → A) → SimEvent A
simAccumE a₀ = simFoldE a₀ (λ f a → f a)

------------------------------------------------------------------------
-- interpret: test an event transformation
------------------------------------------------------------------------

-- Apply a pure event transformation (SimEvent A → SimEvent B)
-- This is the identity — transformations are just functions!
interpret : (SimEvent A → SimEvent B) → SimEvent A → SimEvent B
interpret f = f

-- Collect N ticks from a SimEvent
collectN : ℕ → SimEvent A → SimEvent A
collectN zero    _        = []
collectN (suc n) []       = [] ∷ collectN n []
collectN (suc n) (x ∷ xs) = x ∷ collectN n xs

------------------------------------------------------------------------
-- interpretApp: test a reactive app as pure function
------------------------------------------------------------------------

-- Given update function, initial model, and event stream of messages,
-- produce list of models after each tick
interpretApp : (B → A → A) → A → SimEvent B → List A
interpretApp update model [] = []
interpretApp update model (tick ∷ rest) =
  let model' = applyAll update model tick
  in model' ∷ interpretApp update model' rest
  where
    applyAll : (B → A → A) → A → List B → A
    applyAll update m [] = m
    applyAll update m (msg ∷ msgs) = applyAll update (update msg m) msgs

------------------------------------------------------------------------
-- Test examples (propositional equality proofs)
------------------------------------------------------------------------

-- mapE test
test-mapE : simMapE suc ((1 ∷ 2 ∷ []) ∷ [] ∷ (3 ∷ []) ∷ [])
          ≡ ((2 ∷ 3 ∷ []) ∷ [] ∷ (4 ∷ []) ∷ [])
test-mapE = refl

-- filterE test
test-filterE : simFilterE (λ { zero → false ; (suc _) → true })
                ((0 ∷ 1 ∷ 2 ∷ []) ∷ (3 ∷ 0 ∷ []) ∷ [])
             ≡ ((1 ∷ 2 ∷ []) ∷ (3 ∷ []) ∷ [])
test-filterE = refl

-- foldE test: count events
test-foldE : simFoldE 0 (λ _ n → suc n)
              ((1 ∷ []) ∷ (2 ∷ 3 ∷ []) ∷ [] ∷ (4 ∷ []) ∷ [])
           ≡ ((1 ∷ []) ∷ (2 ∷ 3 ∷ []) ∷ [] ∷ (4 ∷ []) ∷ [])
test-foldE = refl

-- accumE test: apply increment functions
test-accumE : simAccumE 0 ((suc ∷ []) ∷ (suc ∷ suc ∷ []) ∷ [])
            ≡ ((1 ∷ []) ∷ (2 ∷ 3 ∷ []) ∷ [])
test-accumE = refl

-- interpretApp test
test-app : interpretApp (λ _ n → suc n) 0
            ((1 ∷ []) ∷ (2 ∷ 3 ∷ []) ∷ [] ∷ [])
         ≡ (1 ∷ 3 ∷ 3 ∷ [])
test-app = refl

-- merge test
test-merge : simMerge ((1 ∷ []) ∷ [] ∷ (3 ∷ []) ∷ [])
                      ((10 ∷ []) ∷ (20 ∷ []) ∷ [])
           ≡ ((1 ∷ 10 ∷ []) ∷ (20 ∷ []) ∷ (3 ∷ []) ∷ [])
test-merge = refl
