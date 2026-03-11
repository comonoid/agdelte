{-# OPTIONS --without-K --guardedness #-}

-- SharedAgent tests — propositional equality proofs
-- Tests for SharedAgent, LinearAgent, Registry operations

module Agdelte.Test.SharedAgentTest where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.String using (String)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Function using (id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Agdelte.Concurrent.Agent
open import Agdelte.Concurrent.SharedAgent

------------------------------------------------------------------------
-- Test agent: simple counter
------------------------------------------------------------------------

counterAgent : Agent ℕ ℕ ℕ
counterAgent = mkAgent 0 id (λ s i → s + i)

------------------------------------------------------------------------
-- SharedAgent tests
------------------------------------------------------------------------

sharedCounter : SharedAgent ℕ ℕ
sharedCounter = share counterAgent

test-peek-shared : peekShared sharedCounter ≡ 0
test-peek-shared = refl

test-step-shared : proj₂ (stepShared sharedCounter 5) ≡ 5
test-step-shared = refl

-- Step then peek on the resulting agent
test-step-then-peek :
  let (sa' , _) = stepShared sharedCounter 3
  in peekShared sa' ≡ 3
test-step-then-peek = refl

-- Two steps
test-two-steps :
  let (sa₁ , _) = stepShared sharedCounter 3
      (sa₂ , _) = stepShared sa₁ 7
  in peekShared sa₂ ≡ 10
test-two-steps = refl

------------------------------------------------------------------------
-- LinearAgent tests
------------------------------------------------------------------------

linearCounter : LinearAgent ℕ ℕ
linearCounter = asLinear counterAgent

test-use-linear : useLinear linearCounter 5 ≡ 5
test-use-linear = refl

------------------------------------------------------------------------
-- Registry tests
------------------------------------------------------------------------

testRegistry : Registry
testRegistry =
  mkNamed "counter" "/counter" sharedCounter ∷
  mkNamed "backup"  "/backup"  sharedCounter ∷
  []

test-lookup-found : map agentName (lookupAgent "counter" testRegistry) ≡ just "counter"
test-lookup-found = refl

test-lookup-second : map agentName (lookupAgent "backup" testRegistry) ≡ just "backup"
test-lookup-second = refl

test-lookup-missing : lookupAgent "nonexistent" testRegistry ≡ nothing
test-lookup-missing = refl

------------------------------------------------------------------------
-- Composition tests
------------------------------------------------------------------------

-- Pipeline composition
sharedPipeline : SharedAgent ℕ ℕ
sharedPipeline = sharedCounter >>>shared sharedCounter

test-pipeline-peek : peekShared sharedPipeline ≡ 0
test-pipeline-peek = refl

-- Fanout composition
sharedFanout : SharedAgent ℕ (ℕ × ℕ)
sharedFanout = fanoutShared sharedCounter sharedCounter

test-fanout-peek : peekShared sharedFanout ≡ (0 , 0)
test-fanout-peek = refl
