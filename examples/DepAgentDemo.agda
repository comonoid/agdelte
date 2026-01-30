{-# OPTIONS --without-K --guardedness #-}

-- DepAgentDemo: dependent agents where input type depends on state
--
-- Shows: DepAgent, embed, dep⊕, dep&, stepDep, throughDep, DepAgentLens
--
-- Scenario: a vending machine with state-dependent commands.
--   Idle    → accepts Insert (coin)
--   Ready   → accepts Select (product) or Cancel
--   No "select" in Idle, no "insert" in Ready — enforced by types.

module DepAgentDemo where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.String using (String; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (id; const; _∘_)

open import Agdelte.Concurrent.Agent as Fixed using (Agent; mkAgent)
open import Agdelte.Concurrent.DepAgent

------------------------------------------------------------------------
-- 1. Vending machine: state-dependent input
------------------------------------------------------------------------

-- Machine phases
data Phase : Set where
  idle  : Phase    -- waiting for coin
  ready : Phase    -- coin inserted, waiting for selection

-- Commands depend on current phase
Cmd : Phase → Set
Cmd idle  = ⊤         -- insert coin (unit = just do it)
Cmd ready = String     -- select product by name, or "cancel"

-- Machine state: phase + accumulated coins
record VendState : Set where
  constructor mkVS
  field
    phase : Phase
    coins : ℕ

open VendState public

-- Observation = current phase
vendObserve : VendState → Phase
vendObserve = phase

-- Step: depends on observation (phase)
vendStep : (s : VendState) → Cmd (vendObserve s) → VendState
vendStep (mkVS idle n)  tt      = mkVS ready (suc n)    -- insert coin → ready
vendStep (mkVS ready n) "cancel" = mkVS idle n           -- cancel → back to idle
vendStep (mkVS ready n) _       = mkVS idle zero         -- select → dispense, reset

-- The vending machine as a DepAgent
vendingMachine : DepAgent VendState Phase Cmd
vendingMachine = record
  { state   = mkVS idle zero
  ; observe = vendObserve
  ; step    = vendStep
  }

------------------------------------------------------------------------
-- 2. Stepping through the protocol
------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Initially idle
_ : observe vendingMachine (state vendingMachine) ≡ idle
_ = refl

-- After inserting coin: ready
private
  step1-result : DepAgent VendState Phase Cmd × Phase
  step1-result = stepDep vendingMachine tt

  vm1 : DepAgent VendState Phase Cmd
  vm1 = proj₁ step1-result

  _ : proj₂ step1-result ≡ ready
  _ = refl

  -- After selecting: back to idle, coins reset
  step2-result : DepAgent VendState Phase Cmd × Phase
  step2-result = stepDep vm1 "cola"

  _ : proj₂ step2-result ≡ idle
  _ = refl

  -- Coins after: 0 (dispensed)
  _ : coins (state (proj₁ step2-result)) ≡ zero
  _ = refl

  -- Cancel path: insert → cancel → idle, coins preserved
  cancel-result : DepAgent VendState Phase Cmd × Phase
  cancel-result = stepDep vm1 "cancel"

  _ : proj₂ cancel-result ≡ idle
  _ = refl

  _ : coins (state (proj₁ cancel-result)) ≡ 1
  _ = refl

------------------------------------------------------------------------
-- 3. embed: fixed-fiber Agent as DepAgent
------------------------------------------------------------------------

-- A simple counter as fixed-fiber Agent
fixedCounter : Agent ℕ ⊤ ℕ
fixedCounter = mkAgent zero id (λ n _ → suc n)

-- Embed into DepAgent with constant fiber (const ⊤)
depCounter : DepAgent ℕ ℕ (const ⊤)
depCounter = embed fixedCounter

-- Same behavior:
_ : observe depCounter (state depCounter) ≡ zero
_ = refl

------------------------------------------------------------------------
-- 4. dep⊕: exact internal choice
------------------------------------------------------------------------

-- Either vending machine OR counter, no wasted input types.
-- When in vending machine mode, input is Cmd (phase-dependent).
-- When in counter mode, input is ⊤.
-- No mismatch no-op — the exact right type is required.

vendOrCount : DepAgent (VendState ⊎ ℕ) (Phase ⊎ ℕ) (depI Cmd (const ⊤))
vendOrCount = dep⊕ vendingMachine depCounter

-- Initially in vending machine mode (inj₁)
_ : observe vendOrCount (state vendOrCount) ≡ inj₁ idle
_ = refl

------------------------------------------------------------------------
-- 5. dep&: exact external choice
------------------------------------------------------------------------

-- Both vending machine AND counter observable.
-- Input: either Cmd (for vending machine) or ⊤ (for counter).
vendAndCount : DepAgent (VendState × ℕ) (Phase × ℕ) (λ { (p , n) → Cmd p ⊎ ⊤ })
vendAndCount = dep& vendingMachine depCounter

-- Initially: (idle, 0)
_ : observe vendAndCount (state vendAndCount) ≡ (idle , zero)
_ = refl

------------------------------------------------------------------------
-- 6. DepAgentLens + throughDep: interface transformation
------------------------------------------------------------------------

-- A lens that maps Phase to String
data Label : Set where
  waiting  : Label
  choosing : Label

phaseToLabel : Phase → Label
phaseToLabel idle  = waiting
phaseToLabel ready = choosing

-- LabelCmd: commands for labelled interface
LabelCmd : Label → Set
LabelCmd waiting  = ⊤       -- same as Cmd idle
LabelCmd choosing = String   -- same as Cmd ready

-- The lens: Phase → Label, with command mapping back
vendLens : DepAgentLens Cmd LabelCmd
vendLens = record
  { fwd = phaseToLabel
  ; bwd = λ { idle  tt  → tt      -- LabelCmd waiting = ⊤ → Cmd idle = ⊤
            ; ready cmd → cmd     -- LabelCmd choosing = String → Cmd ready = String
            }
  }

-- Apply lens: vending machine with Label interface
labelledVending : DepAgent VendState Label LabelCmd
labelledVending = throughDep vendLens vendingMachine

-- Same behavior, different types
_ : observe labelledVending (state labelledVending) ≡ waiting
_ = refl

------------------------------------------------------------------------
-- Summary
------------------------------------------------------------------------

-- This example demonstrates:
-- 1. DepAgent: input type depends on current observation (Phase → Cmd)
-- 2. stepDep: type-safe stepping (can't send wrong command for current phase)
-- 3. embed: any Agent is a DepAgent with const fiber
-- 4. dep⊕: exact internal choice (no wasted input arms)
-- 5. dep&: exact external choice (both observable)
-- 6. throughDep + DepAgentLens: interface transformation for dependent agents
