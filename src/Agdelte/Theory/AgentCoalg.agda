{-# OPTIONS --without-K --guardedness #-}

-- Formal correspondence: Agent S I O ↔ Coalg (Mono O I)
--
-- Agent IS a coalgebra of the polynomial p(y) = O × y^I
-- This module makes the correspondence explicit and proves it.

module Agdelte.Theory.AgentCoalg where

open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Function using (id; _∘_; const)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Agdelte.Theory.Poly
open import Agdelte.Concurrent.Agent as A using (Agent; mkAgent)

------------------------------------------------------------------------
-- The polynomial for Agent S I O: p(y) = O × y^I = Mono O I
------------------------------------------------------------------------

AgentPoly : Set → Set → Poly
AgentPoly O I = Mono O I

-- Verify: ⟦ AgentPoly O I ⟧ S = Σ O (λ _ → I → S) = O × (I → S)
-- This is exactly what Agent.observe + Agent.step give us.

------------------------------------------------------------------------
-- Agent → Coalg
------------------------------------------------------------------------

agentToCoalg : ∀ {S I O : Set} → Agent S I O → Coalg (AgentPoly O I)
agentToCoalg a = mkCoalg
  _
  (A.observe a)
  (A.step a)

------------------------------------------------------------------------
-- Coalg → Agent
------------------------------------------------------------------------

-- Coalg → Agent requires providing an initial state (Coalg doesn't carry one).
-- The correspondence is between the *structure* (observe + step), not initial state.
fromCoalg : ∀ {I O : Set} (c : Coalg (Mono O I)) → Coalg.State c → Agent (Coalg.State c) I O
fromCoalg c s₀ = mkAgent s₀ (Coalg.observe c) (Coalg.update c)

------------------------------------------------------------------------
-- Structure correspondence (without initial state)
------------------------------------------------------------------------

-- An AgentStructure is Agent minus initial state.
record AgentStructure (S I O : Set) : Set where
  field
    observe : S → O
    step    : S → I → S

-- Coalg (Mono O I) with carrier S is exactly AgentStructure S I O.

structureToCoalg : ∀ {S I O} → AgentStructure S I O → Coalg (Mono O I)
structureToCoalg {S} as = mkCoalg S (AgentStructure.observe as) (AgentStructure.step as)

-- Coalg → AgentStructure (direct version with explicit carrier):
fromCoalgStr : ∀ {I O : Set} (c : Coalg (Mono O I)) → AgentStructure (Coalg.State c) I O
fromCoalgStr c = record
  { observe = Coalg.observe c
  ; step    = Coalg.update c
  }

toCoalgStr : ∀ {S I O : Set} → AgentStructure S I O → Coalg (Mono O I)
toCoalgStr {S} as = mkCoalg S (AgentStructure.observe as) (AgentStructure.step as)

------------------------------------------------------------------------
-- Round-trip proofs
------------------------------------------------------------------------

-- AgentStructure → Coalg → AgentStructure = id
round-trip-str : ∀ {S I O} (as : AgentStructure S I O)
               → fromCoalgStr (toCoalgStr as) ≡ as
round-trip-str _ = refl

-- Agent → Coalg → AgentStructure preserves observe and step
agent-coalg-observe : ∀ {S I O} (a : Agent S I O) (s : S)
                    → Coalg.observe (agentToCoalg a) s ≡ A.observe a s
agent-coalg-observe _ _ = refl

agent-coalg-step : ∀ {S I O} (a : Agent S I O) (s : S) (i : I)
                 → Coalg.update (agentToCoalg a) s i ≡ A.step a s i
agent-coalg-step _ _ _ = refl

------------------------------------------------------------------------
-- AgentLens ↔ Poly.Lens for monomial case
------------------------------------------------------------------------

open import Agdelte.Concurrent.Wiring using (AgentLens)

-- AgentLens I₁ O₁ I₂ O₂ corresponds to Poly.Lens (Mono O₁ I₁) (Mono O₂ I₂)
-- Both have: fwd : O₁ → O₂ and bwd : O₁ → I₂ → I₁

agentLensToPolyLens : ∀ {I₁ O₁ I₂ O₂ : Set}
                    → AgentLens I₁ O₁ I₂ O₂
                    → Lens (Mono O₁ I₁) (Mono O₂ I₂)
agentLensToPolyLens al = mkLens
  (AgentLens.fwd al)
  (AgentLens.bwd al)

polyLensToAgentLens : ∀ {I₁ O₁ I₂ O₂ : Set}
                    → Lens (Mono O₁ I₁) (Mono O₂ I₂)
                    → AgentLens I₁ O₁ I₂ O₂
polyLensToAgentLens pl = record
  { fwd = Lens.onPos pl
  ; bwd = Lens.onDir pl
  }

-- Round-trips are identity (definitional)
al-round-trip : ∀ {I₁ O₁ I₂ O₂ : Set} (al : AgentLens I₁ O₁ I₂ O₂)
              → polyLensToAgentLens (agentLensToPolyLens al) ≡ al
al-round-trip _ = refl

pl-round-trip : ∀ {I₁ O₁ I₂ O₂ : Set} (pl : Lens (Mono O₁ I₁) (Mono O₂ I₂))
              → agentLensToPolyLens (polyLensToAgentLens pl) ≡ pl
pl-round-trip _ = refl
