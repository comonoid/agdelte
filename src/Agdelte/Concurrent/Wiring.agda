{-# OPTIONS --without-K --guardedness #-}

-- Wiring: polynomial lens composition of agents
--
-- Layer 1: AgentLens — morphism between agent interfaces (polynomial lens)
-- Layer 2: Simple combinators — >>>, ***, fanout, loop
--          defined via AgentLens but usable without knowing about lenses
--
-- All types stay in Set. No HList, no universe issues.
-- Error messages are plain unification failures on concrete types.

module Agdelte.Concurrent.Wiring where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (_∘_; id; const)

open import Agdelte.Concurrent.Agent

private
  variable
    S S₁ S₂ S₃ I I₁ I₂ I' O O₁ O₂ O' M : Set

------------------------------------------------------------------------
-- Layer 1: AgentLens — polynomial lens between agent interfaces
------------------------------------------------------------------------

-- A lens between two agent interfaces.
-- fwd maps observations (covariant, positions)
-- bwd maps inputs (contravariant, directions) — may depend on current observation
--
-- This is a morphism in the category of polynomial functors:
--   p(y) = O₁ × y^{I₁}  →  q(y) = O₂ × y^{I₂}
-- where fwd : O₁ → O₂, bwd : O₁ → I₂ → I₁

record AgentLens (I₁ O₁ I₂ O₂ : Set) : Set where
  constructor mkAgentLens
  field
    fwd : O₁ → O₂
    bwd : O₁ → I₂ → I₁

open AgentLens public

-- Apply lens to agent: change its external interface
through : AgentLens I O I' O' → Agent S I O → Agent S I' O'
through φ a = record
  { state   = state a
  ; observe = λ s → fwd φ (observe a s)
  ; step    = λ s i' → step a s (bwd φ (observe a s) i')
  }

------------------------------------------------------------------------
-- AgentLens identity and composition
------------------------------------------------------------------------

-- Identity lens: no change to interface
idAL : AgentLens I O I O
idAL = mkAgentLens id (const id)

-- Compose lenses: φ then ψ
_∘AL_ : AgentLens I₂ O₂ I' O' → AgentLens I₁ O₁ I₂ O₂ → AgentLens I₁ O₁ I' O'
ψ ∘AL φ = mkAgentLens
  (fwd ψ ∘ fwd φ)
  (λ o₁ i' → bwd φ o₁ (bwd ψ (fwd φ o₁) i'))

------------------------------------------------------------------------
-- Layer 2: Simple combinators
------------------------------------------------------------------------

-- Pipeline: output of first feeds input of second
-- Type error if O₁ ≠ I₂ — message: "Cannot unify O₁ with I₂"
infixr 6 _>>>_
_>>>_ : Agent S₁ I M → Agent S₂ M O → Agent (S₁ × S₂) I O
a >>> b = record
  { state   = state a , state b
  ; observe = λ { (s₁ , s₂) → observe b s₂ }
  ; step    = λ { (s₁ , s₂) i →
      let s₁' = step a s₁ i
      in  s₁' , step b s₂ (observe a s₁') }
  }

-- Parallel: independent agents, independent interfaces
infixr 7 _***_
_***_ : Agent S₁ I₁ O₁ → Agent S₂ I₂ O₂ → Agent (S₁ × S₂) (I₁ × I₂) (O₁ × O₂)
a *** b = record
  { state   = state a , state b
  ; observe = λ { (s₁ , s₂) → observe a s₁ , observe b s₂ }
  ; step    = λ { (s₁ , s₂) (i₁ , i₂) → step a s₁ i₁ , step b s₂ i₂ }
  }

-- Fan-out: same input to both agents
fanout : Agent S₁ I O₁ → Agent S₂ I O₂ → Agent (S₁ × S₂) I (O₁ × O₂)
fanout a b = record
  { state   = state a , state b
  ; observe = λ { (s₁ , s₂) → observe a s₁ , observe b s₂ }
  ; step    = λ { (s₁ , s₂) i → step a s₁ i , step b s₂ i }
  }

-- Feedback: output feeds back as part of input
-- Agent has interface (I × O) → O; loop closes the O → O loop
loop : Agent S (I × O) O → Agent S I O
loop a = record
  { state   = state a
  ; observe = observe a
  ; step    = λ s i → step a s (i , observe a s)
  }

------------------------------------------------------------------------
-- Linear logic connectives
------------------------------------------------------------------------

-- & (with / external choice): both agents observable, input goes to one
-- Categorical product in Poly: positions multiply, directions sum
-- Use case: server offers two services, client picks per request
infixr 5 _&_
_&_ : Agent S₁ I₁ O₁ → Agent S₂ I₂ O₂ → Agent (S₁ × S₂) (I₁ ⊎ I₂) (O₁ × O₂)
a & b = record
  { state   = state a , state b
  ; observe = λ { (s₁ , s₂) → observe a s₁ , observe b s₂ }
  ; step    = λ { (s₁ , s₂) (inj₁ i₁) → step a s₁ i₁ , s₂
                ; (s₁ , s₂) (inj₂ i₂) → s₁ , step b s₂ i₂ }
  }

-- ⊕ (plus / internal choice): one agent active, picked by state tag
-- Coproduct in Poly: positions sum, directions inherited per side
-- Use case: system switches between two modes (e.g., editing vs viewing)
-- Note: input tag must match state tag; mismatched input is no-op (safe)
infixr 5 _⊕_
_⊕_ : Agent S₁ I₁ O₁ → Agent S₂ I₂ O₂ → Agent (S₁ ⊎ S₂) (I₁ ⊎ I₂) (O₁ ⊎ O₂)
a ⊕ b = record
  { state   = inj₁ (state a)
  ; observe = λ { (inj₁ s₁) → inj₁ (observe a s₁)
                ; (inj₂ s₂) → inj₂ (observe b s₂) }
  ; step    = λ { (inj₁ s₁) (inj₁ i₁) → inj₁ (step a s₁ i₁)
                ; (inj₂ s₂) (inj₂ i₂) → inj₂ (step b s₂ i₂)
                ; s _                    → s }   -- mismatched tag: no-op
  }

-- Lenses for accessing & components
-- Selecting left service of a & b:
--   through selectLeft (a & b) : Agent (S₁ × S₂) I₁ O₁
selectLeft : AgentLens (I₁ ⊎ I₂) (O₁ × O₂) I₁ O₁
selectLeft = mkAgentLens proj₁ (λ _ → inj₁)

selectRight : AgentLens (I₁ ⊎ I₂) (O₁ × O₂) I₂ O₂
selectRight = mkAgentLens proj₂ (λ _ → inj₂)

-- Unit agents (identities for & and ⊗)
-- Terminal: no input, unit output (identity for &)
terminal : Agent ⊤ I ⊤
terminal = mkAgent tt (λ _ → tt) (λ _ _ → tt)

------------------------------------------------------------------------
-- Interface transformers (trivial lenses)
------------------------------------------------------------------------

-- Pre-compose input transformation (contravariant)
-- Already exists as mapInput in Agent.agda, re-exported for completeness
mapI : (I' → I) → Agent S I O → Agent S I' O
mapI = mapInput

-- Post-compose output transformation (covariant)
mapO : (O → O') → Agent S I O → Agent S I O'
mapO = mapObserve

-- Both at once (via AgentLens)
remap : (I' → I) → (O → O') → Agent S I O → Agent S I' O'
remap fi fo = through (mkAgentLens fo (const fi))

------------------------------------------------------------------------
-- Derived combinators
------------------------------------------------------------------------

-- Swap inputs
swap : Agent S (I₁ × I₂) O → Agent S (I₂ × I₁) O
swap a = mapI (λ { (i₂ , i₁) → i₁ , i₂ }) a

-- Constant agent: ignores input, always observes initial value
constAgent : ∀ {I} → O → Agent O I O
constAgent o = mkAgent o id (λ s _ → s)


------------------------------------------------------------------------
-- Existential wrapper: hide state type
------------------------------------------------------------------------

-- For collections of agents with different state types
record SomeAgent (I O : Set) : Set₁ where
  constructor someAgent
  field
    {State} : Set
    agent : Agent State I O

open SomeAgent public

-- Pack agent
pack : Agent S I O → SomeAgent I O
pack a = someAgent a

-- Compose packed agents
_>>>ₛ_ : SomeAgent I M → SomeAgent M O → SomeAgent I O
someAgent a >>>ₛ someAgent b = someAgent (a >>> b)

_***ₛ_ : SomeAgent I₁ O₁ → SomeAgent I₂ O₂ → SomeAgent (I₁ × I₂) (O₁ × O₂)
someAgent a ***ₛ someAgent b = someAgent (a *** b)

_&ₛ_ : SomeAgent I₁ O₁ → SomeAgent I₂ O₂ → SomeAgent (I₁ ⊎ I₂) (O₁ × O₂)
someAgent a &ₛ someAgent b = someAgent (a & b)

_⊕ₛ_ : SomeAgent I₁ O₁ → SomeAgent I₂ O₂ → SomeAgent (I₁ ⊎ I₂) (O₁ ⊎ O₂)
someAgent a ⊕ₛ someAgent b = someAgent (a ⊕ b)
