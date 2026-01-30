{-# OPTIONS --without-K --guardedness #-}

-- AgentWiring: demonstrates Agent-level wiring combinators
--
-- Shows: >>>, &, ⊕, ***, fanout, loop, through, selectLeft/selectRight
-- All from Agdelte.Concurrent.Wiring
--
-- Scenario: a data processing pipeline
--   sensor → scaler → classifier
-- with parallel composition and interface transformation via AgentLens.

module AgentWiring where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Show using (show)
open import Data.String using (String; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Function using (id; const; _∘_)

open import Agdelte.Concurrent.Agent
open import Agdelte.Concurrent.Wiring

------------------------------------------------------------------------
-- Basic agents
------------------------------------------------------------------------

-- Counter: counts how many inputs it has received
counter : Agent ℕ ⊤ ℕ
counter = mkAgent zero id (λ n _ → suc n)

-- Doubler: stores last doubled value
doublerAgent : Agent ℕ ℕ ℕ
doublerAgent = mkAgent zero id (λ _ n → n * 2)

-- Threshold: classifies input as "low" or "high"
thresholdAgent : ℕ → Agent ⊤ ℕ String
thresholdAgent t = mkAgent tt (const "?") classify
  where
    classify : ⊤ → ℕ → ⊤
    classify _ _ = tt

-- Better: an agent that remembers the classification
classifier : ℕ → Agent String ℕ String
classifier threshold = mkAgent "?" id classify
  where
    _≤?_ : ℕ → ℕ → Bool
    zero  ≤? _     = true
    suc _ ≤? zero  = false
    suc m ≤? suc n = m ≤? n

    classify : String → ℕ → String
    classify _ n = if (n ≤? threshold) then "low" else "high"

------------------------------------------------------------------------
-- 1. Pipeline: >>> (sequential composition)
------------------------------------------------------------------------

-- counter >>> doublerAgent : count inputs, then double the count
-- Input: ⊤ (tick), Output: ℕ (doubled count)
countAndDouble : Agent (ℕ × ℕ) ⊤ ℕ
countAndDouble = counter >>> doublerAgent

-- Three-stage: count → double → classify
pipeline : Agent (ℕ × (ℕ × String)) ⊤ String
pipeline = counter >>> (doublerAgent >>> classifier 10)

------------------------------------------------------------------------
-- 2. Parallel: *** (both receive independent inputs)
------------------------------------------------------------------------

-- Two independent counters, each counting separately
twoCounters : Agent (ℕ × ℕ) (⊤ × ⊤) (ℕ × ℕ)
twoCounters = counter *** counter

------------------------------------------------------------------------
-- 3. Fan-out: same input to both agents
------------------------------------------------------------------------

-- Same tick goes to both counters (they always agree)
syncCounters : Agent (ℕ × ℕ) ⊤ (ℕ × ℕ)
syncCounters = fanout counter counter

------------------------------------------------------------------------
-- 4. External choice: & (both observable, input to one)
------------------------------------------------------------------------

-- Offer two services: counter (tick to count) or classifier (number to label)
counterOrClassifier : Agent (ℕ × String) (⊤ ⊎ ℕ) (ℕ × String)
counterOrClassifier = counter & classifier 5

------------------------------------------------------------------------
-- 5. through + selectLeft/selectRight
------------------------------------------------------------------------

-- From the & composition, select just the counter interface:
justCounter : Agent (ℕ × String) ⊤ ℕ
justCounter = through selectLeft counterOrClassifier

-- Or just the classifier interface:
justClassifier : Agent (ℕ × String) ℕ String
justClassifier = through selectRight counterOrClassifier

------------------------------------------------------------------------
-- 6. Custom AgentLens: interface transformation
------------------------------------------------------------------------

-- Lens that converts String input to ℕ (always maps to 1 = "tick")
stringToTick : AgentLens ⊤ ℕ String String
stringToTick = mkAgentLens show (λ _ _ → tt)

-- Apply lens: counter now accepts String, outputs String
stringCounter : Agent ℕ String String
stringCounter = through stringToTick counter

------------------------------------------------------------------------
-- 7. Internal choice: ⊕ (one branch active at a time)
------------------------------------------------------------------------

-- Either counting or classifying, switched by state tag
countOrClassify : Agent (ℕ ⊎ String) (⊤ ⊎ ℕ) (ℕ ⊎ String)
countOrClassify = counter ⊕ classifier 5

------------------------------------------------------------------------
-- 8. Loop: feedback
------------------------------------------------------------------------

-- Self-feeding counter: output feeds back as part of next input
-- Agent with (ℕ × ℕ) input, ℕ output; loop closes the ℕ → ℕ feedback
selfCounter : Agent ℕ ℕ ℕ
selfCounter = loop feedbackAgent
  where
    -- Takes (external-input, feedback-from-output) and produces count
    feedbackAgent : Agent ℕ (ℕ × ℕ) ℕ
    feedbackAgent = mkAgent zero id (λ _ p → proj₁ p + proj₂ p)

------------------------------------------------------------------------
-- 9. mapI / mapO: simple transformations
------------------------------------------------------------------------

-- Wrap counter to accept Bool (true=tick, false=noop)
boolCounter : Agent ℕ Bool ℕ
boolCounter = mapI boolToUnit counter
  where
    boolToUnit : Bool → ⊤
    boolToUnit _ = tt

-- Wrap counter to output String
showingCounter : Agent ℕ ⊤ String
showingCounter = mapO show counter

------------------------------------------------------------------------
-- 10. remap: both at once
------------------------------------------------------------------------

-- Counter with String in, String out
remappedCounter : Agent ℕ String String
remappedCounter = remap (const tt) show counter

------------------------------------------------------------------------
-- 11. SomeAgent: existential wrapper for heterogeneous collections
------------------------------------------------------------------------

-- Pack agents with different state types
agent1 : SomeAgent ⊤ ℕ
agent1 = pack counter

agent2 : SomeAgent ℕ String
agent2 = pack (classifier 5)

-- Compose packed agents
packedPipeline : SomeAgent ⊤ String
packedPipeline = agent1 >>>ₛ agent2

------------------------------------------------------------------------
-- Verification: step through pipeline
------------------------------------------------------------------------

-- Step countAndDouble 3 times and check output
private
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)

  -- Initial observation: doubler starts at 0
  _ : observe countAndDouble (state countAndDouble) ≡ zero
  _ = refl

  -- After 1 tick: counter=1, doubled=2
  step1 : ℕ × ℕ
  step1 = step countAndDouble (state countAndDouble) tt

  _ : observe countAndDouble step1 ≡ 2
  _ = refl

  -- After 2 ticks: counter=2, doubled=4
  step2 : ℕ × ℕ
  step2 = step countAndDouble step1 tt

  _ : observe countAndDouble step2 ≡ 4
  _ = refl

  -- fanout: both counters in sync
  _ : observe syncCounters (state syncCounters) ≡ (zero , zero)
  _ = refl

  sync1 : ℕ × ℕ
  sync1 = step syncCounters (state syncCounters) tt

  _ : observe syncCounters sync1 ≡ (1 , 1)
  _ = refl

  -- through selectLeft on &: only counter increments
  _ : observe justCounter (state justCounter) ≡ zero
  _ = refl

  just1 : ℕ × String
  just1 = step justCounter (state justCounter) tt

  _ : observe justCounter just1 ≡ 1
  _ = refl
