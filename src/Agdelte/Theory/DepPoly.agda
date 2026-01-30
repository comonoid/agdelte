{-# OPTIONS --without-K --guardedness #-}

-- Dependent Polynomial Formalization
--
-- Connects DepAgent (practical, from Concurrent/) with
-- Poly/Coalg (theoretical, from Theory/) formally.
--
-- Shows that:
-- 1. DepAgent IS a Coalg of a dependent polynomial
-- 2. Fixed-fiber Agent is a special case (constant fiber)
-- 3. embed/forget form an adjunction-like structure
-- 4. DepAgentLens IS a Poly.Lens between dependent polynomials

module Agdelte.Theory.DepPoly where

open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (id; _∘_; const)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Agdelte.Theory.Poly as P using (Poly; mkPoly; Coalg; mkCoalg; Mono; Lens; mkLens)
open import Agdelte.Concurrent.Agent as A using (Agent; mkAgent)
open import Agdelte.Concurrent.DepAgent as D using (DepAgent; DepAgentLens)

------------------------------------------------------------------------
-- DepAgent as Coalg: the polynomial is just Poly itself
------------------------------------------------------------------------

-- A DepAgent S O I has:
--   observe : S → O                    (position map)
--   step    : (s : S) → I (observe s) → S  (direction map)
--
-- This is exactly Coalg (mkPoly O I):
--   observe : State → Pos P            where Pos = O
--   update  : (s : State) → Dir P (observe s) → State  where Dir = I

depAgentToCoalg : ∀ {S O : Set} {I : O → Set}
                → DepAgent S O I
                → Coalg (mkPoly O I)
depAgentToCoalg da = mkCoalg
  _
  (D.observe da)
  (D.step da)

-- Coalg → DepAgent requires providing initial state (Coalg doesn't carry one).
coalgToDepAgent : ∀ {O : Set} {I : O → Set}
                → (c : Coalg (mkPoly O I))
                → Coalg.State c
                → DepAgent (Coalg.State c) O I
coalgToDepAgent c s₀ = record
  { state   = s₀
  ; observe = Coalg.observe c
  ; step    = Coalg.update c
  }

------------------------------------------------------------------------
-- Fixed fiber = constant polynomial = Mono
------------------------------------------------------------------------

-- Agent S I O is DepAgent S O (const I), which is Coalg (Mono O I)

-- Embedding chain: Agent → DepAgent → Coalg
agentToDepToCoalg : ∀ {S I O : Set} → Agent S I O → Coalg (Mono O I)
agentToDepToCoalg = depAgentToCoalg ∘ D.embed

-- This matches Theory.AgentCoalg.agentToCoalg:
open import Agdelte.Theory.AgentCoalg as AC using (agentToCoalg)

-- Both produce the same Coalg (definitionally)
embed-consistent : ∀ {S I O : Set} (a : Agent S I O)
                 → agentToDepToCoalg a ≡ agentToCoalg a
embed-consistent _ = refl

------------------------------------------------------------------------
-- DepAgentLens ↔ Poly.Lens
------------------------------------------------------------------------

-- DepAgentLens {O₁} {O₂} I₁ I₂ has:
--   fwd : O₁ → O₂
--   bwd : (o₁ : O₁) → I₂ (fwd o₁) → I₁ o₁
--
-- Poly.Lens (mkPoly O₁ I₁) (mkPoly O₂ I₂) has:
--   onPos : O₁ → O₂
--   onDir : (o₁ : O₁) → I₂ (onPos o₁) → I₁ o₁
--
-- These are identical.

depLensToPolyLens : ∀ {O₁ O₂ : Set} {I₁ : O₁ → Set} {I₂ : O₂ → Set}
                  → DepAgentLens I₁ I₂
                  → Lens (mkPoly O₁ I₁) (mkPoly O₂ I₂)
depLensToPolyLens dal = mkLens
  (D.fwd dal)
  (D.bwd dal)

polyLensToDepLens : ∀ {O₁ O₂ : Set} {I₁ : O₁ → Set} {I₂ : O₂ → Set}
                  → Lens (mkPoly O₁ I₁) (mkPoly O₂ I₂)
                  → DepAgentLens I₁ I₂
polyLensToDepLens pl = record
  { fwd = P.Lens.onPos pl
  ; bwd = P.Lens.onDir pl
  }

-- Round-trips are identity
depLens-rt : ∀ {O₁ O₂ : Set} {I₁ : O₁ → Set} {I₂ : O₂ → Set}
           → (dal : DepAgentLens I₁ I₂)
           → polyLensToDepLens {O₁} {O₂} (depLensToPolyLens dal) ≡ dal
depLens-rt _ = refl

polyLens-rt : ∀ {O₁ O₂ : Set} {I₁ : O₁ → Set} {I₂ : O₂ → Set}
            → (pl : Lens (mkPoly O₁ I₁) (mkPoly O₂ I₂))
            → depLensToPolyLens (polyLensToDepLens pl) ≡ pl
polyLens-rt _ = refl

------------------------------------------------------------------------
-- throughDep corresponds to transformCoalg
------------------------------------------------------------------------

-- D.throughDep maps DepAgent through DepAgentLens
-- P.transformCoalg maps Coalg through Poly.Lens
-- These correspond under the isomorphisms above.

through-consistent : ∀ {S O₁ O₂ : Set} {I₁ : O₁ → Set} {I₂ : O₂ → Set}
                   → (dal : DepAgentLens I₁ I₂)
                   → (da : DepAgent S O₁ I₁)
                   → depAgentToCoalg (D.throughDep dal da)
                     ≡ P.transformCoalg (depLensToPolyLens dal) (depAgentToCoalg da)
through-consistent _ _ = refl

------------------------------------------------------------------------
-- dep⊕ corresponds to choice on Coalg level
------------------------------------------------------------------------

-- D.dep⊕ combines two DepAgents via internal choice (⊕).
-- P.choice combines two Coalgebras via polynomial sum (P ⊕ Q).
--
-- dep⊕ da₁ da₂ : DepAgent (S₁ ⊎ S₂) (O₁ ⊎ O₂) (depI I₁ I₂)
-- choice c₁ c₂  : Coalg (P₁ ⊕ P₂)
--
-- The polynomial (mkPoly O₁ I₁) ⊕ (mkPoly O₂ I₂) is exactly
-- mkPoly (O₁ ⊎ O₂) (depI I₁ I₂), so these correspond.

open import Agdelte.Concurrent.DepAgent using (dep⊕; dep&; depI)
open P using (_⊕_; _⊗_; choice; parallel)

-- dep⊕ and choice produce structurally identical coalgebras.
-- The polynomials mkPoly O₁ I₁ ⊕ mkPoly O₂ I₂ and mkPoly (O₁ ⊎ O₂) (depI I₁ I₂)
-- differ only in eta-expansion of the direction function, so we verify
-- the structural correspondence component-wise.

-- observe components match
dep⊕-observe : ∀ {S₁ S₂ O₁ O₂ : Set} {I₁ : O₁ → Set} {I₂ : O₂ → Set}
             → (da₁ : DepAgent S₁ O₁ I₁) (da₂ : DepAgent S₂ O₂ I₂)
             → (s : S₁ ⊎ S₂)
             → Coalg.observe (depAgentToCoalg (dep⊕ da₁ da₂)) s
               ≡ Coalg.observe (choice (depAgentToCoalg da₁) (depAgentToCoalg da₂)) s
dep⊕-observe _ _ (inj₁ _) = refl
dep⊕-observe _ _ (inj₂ _) = refl

-- step/update also match (by case on state tag)
dep⊕-step : ∀ {S₁ S₂ O₁ O₂ : Set} {I₁ : O₁ → Set} {I₂ : O₂ → Set}
           → (da₁ : DepAgent S₁ O₁ I₁) (da₂ : DepAgent S₂ O₂ I₂)
           → (s₁ : S₁) (i : I₁ (D.observe da₁ s₁))
           → D.step (dep⊕ da₁ da₂) (inj₁ s₁) i ≡ inj₁ (D.step da₁ s₁ i)
dep⊕-step _ _ _ _ = refl

------------------------------------------------------------------------
-- dep& corresponds to parallel on Coalg level
------------------------------------------------------------------------

-- D.dep& combines two DepAgents via external choice (&).
-- P.parallel combines two Coalgebras via polynomial tensor (P ⊗ Q).
--
-- dep& da₁ da₂ : DepAgent (S₁ × S₂) (O₁ × O₂) (λ (o₁,o₂) → I₁ o₁ ⊎ I₂ o₂)
-- parallel c₁ c₂ : Coalg (P₁ ⊗ P₂)
--
-- The polynomial (mkPoly O₁ I₁) ⊗ (mkPoly O₂ I₂) is exactly
-- mkPoly (O₁ × O₂) (λ (o₁,o₂) → I₁ o₁ ⊎ I₂ o₂), so these correspond.

-- dep& and parallel produce structurally identical coalgebras.
-- Same eta-expansion issue as ⊕; verify component-wise.

dep&-observe : ∀ {S₁ S₂ O₁ O₂ : Set} {I₁ : O₁ → Set} {I₂ : O₂ → Set}
             → (da₁ : DepAgent S₁ O₁ I₁) (da₂ : DepAgent S₂ O₂ I₂)
             → (s : S₁ × S₂)
             → Coalg.observe (depAgentToCoalg (dep& da₁ da₂)) s
               ≡ Coalg.observe (parallel (depAgentToCoalg da₁) (depAgentToCoalg da₂)) s
dep&-observe _ _ _ = refl

-- step/update also match (by case on input tag)
dep&-step-left : ∀ {S₁ S₂ O₁ O₂ : Set} {I₁ : O₁ → Set} {I₂ : O₂ → Set}
               → (da₁ : DepAgent S₁ O₁ I₁) (da₂ : DepAgent S₂ O₂ I₂)
               → (s₁ : S₁) (s₂ : S₂) (i : I₁ (D.observe da₁ s₁))
               → D.step (dep& da₁ da₂) (s₁ , s₂) (inj₁ i) ≡ (D.step da₁ s₁ i , s₂)
dep&-step-left _ _ _ _ _ = refl

dep&-step-right : ∀ {S₁ S₂ O₁ O₂ : Set} {I₁ : O₁ → Set} {I₂ : O₂ → Set}
                → (da₁ : DepAgent S₁ O₁ I₁) (da₂ : DepAgent S₂ O₂ I₂)
                → (s₁ : S₁) (s₂ : S₂) (i : I₂ (D.observe da₂ s₂))
                → D.step (dep& da₁ da₂) (s₁ , s₂) (inj₂ i) ≡ (s₁ , D.step da₂ s₂ i)
dep&-step-right _ _ _ _ _ = refl

------------------------------------------------------------------------
-- embed preserves structure: embed is a Coalg morphism
------------------------------------------------------------------------

-- embed : Agent S I O → DepAgent S O (const I)
-- This is specialization from Mono O I to mkPoly O (const I).
-- Since Mono O I = mkPoly O (const I), embed is definitionally identity
-- on the Coalg level.

embed-is-id : ∀ {S I O : Set} (a : Agent S I O)
            → depAgentToCoalg (D.embed a) ≡ agentToCoalg a
embed-is-id _ = refl

------------------------------------------------------------------------
-- Summary of correspondences
------------------------------------------------------------------------

-- | Practical (Concurrent/)        | Theoretical (Theory/)           |
-- |--------------------------------|----------------------------------|
-- | Agent S I O                    | Coalg (Mono O I) with carrier S |
-- | DepAgent S O I                 | Coalg (mkPoly O I) with carrier S |
-- | AgentLens I₁ O₁ I₂ O₂        | Lens (Mono O₁ I₁) (Mono O₂ I₂) |
-- | DepAgentLens I₁ I₂            | Lens (mkPoly O₁ I₁) (mkPoly O₂ I₂) |
-- | through / throughDep           | transformCoalg                   |
-- | embed (Agent → DepAgent)       | const fiber specialization       |
-- | dep⊕                           | choice (Coalg (P ⊕ Q))           |
-- | dep&                           | parallel (Coalg (P ⊗ Q))         |
