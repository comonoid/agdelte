{-# OPTIONS --without-K #-}

-- Proof: Big Lens ↔ Poly.Lens
--
-- IOOptic (network-wide optic) has pure structure:
--   peek : O,  over : I → O
--
-- Part 1: Stateful BigLens ≅ Coalg (Mono O I)
--   An agent exposing peek/over with hidden state is a coalgebra.
--
-- Part 2: BigLensMap (morphism between interfaces) ≅ Poly.Lens (Mono O₁ I₁) (Mono O₂ I₂)
--   Mapping observations forward + routing inputs backward = polynomial lens.
--
-- Part 3: Composition and identity preserved.

module Agdelte.Theory.BigLensPolyLens where

open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Agdelte.Theory.Poly as P
open P using (Poly; mkPoly; Mono; Pos; Dir)

------------------------------------------------------------------------
-- Part 1: Stateful BigLens ≅ Coalg (Mono O I)
------------------------------------------------------------------------

-- Pure skeleton of IOOptic: state + observe + step
-- (IOOptic wraps this in IO with String serialization)
record StatefulBigLens (O I : Set) : Set₁ where
  constructor mkStateful
  field
    State : Set
    obs   : State → O
    step  : State → I → State

-- The polynomial for a BigLens interface
BigLensPoly : Set → Set → Poly
BigLensPoly O I = Mono O I

-- Forward
toCoalg : ∀ {O I} → StatefulBigLens O I → P.Coalg (BigLensPoly O I)
toCoalg sb = P.mkCoalg
  (StatefulBigLens.State sb)
  (StatefulBigLens.obs sb)
  (StatefulBigLens.step sb)

-- Backward (needs initial state, since Coalg doesn't store one)
fromCoalg : ∀ {O I} → P.Coalg (BigLensPoly O I) → StatefulBigLens O I
fromCoalg c = mkStateful (P.Coalg.State c) (P.Coalg.observe c) (P.Coalg.update c)

-- Round-trip: observe preserved
coalg-observe : ∀ {O I} (sb : StatefulBigLens O I)
              → P.Coalg.observe (toCoalg sb) ≡ StatefulBigLens.obs sb
coalg-observe _ = refl

-- Round-trip: update preserved
coalg-update : ∀ {O I} (sb : StatefulBigLens O I)
             → P.Coalg.update (toCoalg sb) ≡ StatefulBigLens.step sb
coalg-update _ = refl

-- Round-trip: fromCoalg (toCoalg sb) has same fields
from∘to-state : ∀ {O I} (sb : StatefulBigLens O I)
              → StatefulBigLens.State (fromCoalg (toCoalg sb)) ≡ StatefulBigLens.State sb
from∘to-state _ = refl

from∘to-obs : ∀ {O I} (sb : StatefulBigLens O I)
            → StatefulBigLens.obs (fromCoalg (toCoalg sb)) ≡ StatefulBigLens.obs sb
from∘to-obs _ = refl

from∘to-step : ∀ {O I} (sb : StatefulBigLens O I)
             → StatefulBigLens.step (fromCoalg (toCoalg sb)) ≡ StatefulBigLens.step sb
from∘to-step _ = refl

------------------------------------------------------------------------
-- Part 2: BigLensMap ≅ Poly.Lens (Mono O₁ I₁) (Mono O₂ I₂)
------------------------------------------------------------------------

-- A morphism between two agent interfaces:
-- maps observations forward, routes inputs backward.
-- This is what a "Big Lens" connecting two network nodes does.
record BigLensMap (O₁ I₁ O₂ I₂ : Set) : Set where
  constructor mkBigLensMap
  field
    mapObs : O₁ → O₂                -- map observations (peek)
    mapIn  : O₁ → I₂ → I₁          -- route inputs back (over)

-- Forward: BigLensMap → Poly.Lens
toPolyLens : ∀ {O₁ I₁ O₂ I₂}
           → BigLensMap O₁ I₁ O₂ I₂
           → P.Lens (BigLensPoly O₁ I₁) (BigLensPoly O₂ I₂)
toPolyLens m = P.mkLens (BigLensMap.mapObs m) (BigLensMap.mapIn m)

-- Backward: Poly.Lens → BigLensMap
fromPolyLens : ∀ {O₁ I₁ O₂ I₂}
             → P.Lens (BigLensPoly O₁ I₁) (BigLensPoly O₂ I₂)
             → BigLensMap O₁ I₁ O₂ I₂
fromPolyLens pl = mkBigLensMap (P.Lens.onPos pl) (P.Lens.onDir pl)

-- Round-trip proofs
from∘to-map : ∀ {O₁ I₁ O₂ I₂} (m : BigLensMap O₁ I₁ O₂ I₂)
            → fromPolyLens (toPolyLens m) ≡ m
from∘to-map (mkBigLensMap _ _) = refl

to∘from-map : ∀ {O₁ I₁ O₂ I₂} (pl : P.Lens (BigLensPoly O₁ I₁) (BigLensPoly O₂ I₂))
            → toPolyLens (fromPolyLens pl) ≡ pl
to∘from-map (P.mkLens _ _) = refl

------------------------------------------------------------------------
-- Part 3: Composition and identity preserved
------------------------------------------------------------------------

-- Compose two BigLensMaps
_∘BL_ : ∀ {O₁ I₁ O₂ I₂ O₃ I₃}
       → BigLensMap O₂ I₂ O₃ I₃
       → BigLensMap O₁ I₁ O₂ I₂
       → BigLensMap O₁ I₁ O₃ I₃
inner ∘BL outer = mkBigLensMap
  (BigLensMap.mapObs inner ∘ BigLensMap.mapObs outer)
  (λ o₁ → BigLensMap.mapIn outer o₁ ∘ BigLensMap.mapIn inner (BigLensMap.mapObs outer o₁))

-- Composition corresponds to Poly.Lens composition
comp-preserved : ∀ {O₁ I₁ O₂ I₂ O₃ I₃}
               → (inner : BigLensMap O₂ I₂ O₃ I₃)
               → (outer : BigLensMap O₁ I₁ O₂ I₂)
               → toPolyLens (inner ∘BL outer)
                 ≡ (toPolyLens inner P.∘L toPolyLens outer)
comp-preserved (mkBigLensMap _ _) (mkBigLensMap _ _) = refl

-- Identity
idBigLensMap : ∀ {O I} → BigLensMap O I O I
idBigLensMap = mkBigLensMap id (λ _ → id)

id-preserved : ∀ {O I} → toPolyLens (idBigLensMap {O} {I}) ≡ P.idLens
id-preserved = refl

------------------------------------------------------------------------
-- Corollary: transformCoalg via BigLensMap
------------------------------------------------------------------------

-- A BigLensMap induces a coalgebra transformation (change of interface)
transformBigLens : ∀ {O₁ I₁ O₂ I₂}
                 → BigLensMap O₁ I₁ O₂ I₂
                 → StatefulBigLens O₁ I₁ → StatefulBigLens O₂ I₂
transformBigLens m sb = mkStateful
  (StatefulBigLens.State sb)
  (BigLensMap.mapObs m ∘ StatefulBigLens.obs sb)
  (λ s i₂ → StatefulBigLens.step sb s (BigLensMap.mapIn m (StatefulBigLens.obs sb s) i₂))

-- This corresponds to Poly.transformCoalg
transform-obs : ∀ {O₁ I₁ O₂ I₂}
              → (m : BigLensMap O₁ I₁ O₂ I₂) (sb : StatefulBigLens O₁ I₁)
              → StatefulBigLens.obs (transformBigLens m sb)
                ≡ (BigLensMap.mapObs m ∘ StatefulBigLens.obs sb)
transform-obs _ _ = refl
