{-# OPTIONS --without-K #-}

-- Proof: Reactive.Lens ≅ Poly.Lens for the monomial case
--
-- Reactive.Lens Outer Inner  ≅  Poly.Lens (Mono Outer Outer) (Mono Inner Inner)
--
-- get ↔ onPos,  set ↔ flip onDir

module Agdelte.Theory.OpticPolyLens where

open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Agdelte.Reactive.Lens as R
import Agdelte.Theory.Poly  as P

------------------------------------------------------------------------
-- The monomial polynomial for a type: Mono A A = mkPoly A (λ _ → A)
-- Pos = A (states), Dir = λ _ → A (transitions always carry a value)
------------------------------------------------------------------------

-- Forward: Reactive.Lens → Poly.Lens
toLens : ∀ {Outer Inner : Set}
       → R.Lens Outer Inner
       → P.Lens (P.Mono Outer Outer) (P.Mono Inner Inner)
toLens l = P.mkLens (R.get l) (λ o i → R.set l i o)

-- Backward: Poly.Lens → Reactive.Lens
fromLens : ∀ {Outer Inner : Set}
         → P.Lens (P.Mono Outer Outer) (P.Mono Inner Inner)
         → R.Lens Outer Inner
fromLens pl = R.mkLens (P.onPos pl) (λ i o → P.onDir pl o i)

------------------------------------------------------------------------
-- Round-trip proofs
------------------------------------------------------------------------

-- fromLens (toLens l) ≡ l
from∘to : ∀ {Outer Inner : Set} (l : R.Lens Outer Inner)
        → fromLens (toLens l) ≡ l
from∘to (R.mkLens _ _) = refl

-- toLens (fromLens pl) ≡ pl
to∘from : ∀ {Outer Inner : Set} (pl : P.Lens (P.Mono Outer Outer) (P.Mono Inner Inner))
        → toLens (fromLens pl) ≡ pl
to∘from (P.mkLens _ _) = refl

------------------------------------------------------------------------
-- Composition is preserved
------------------------------------------------------------------------

-- toLens (inner ∘L outer) ≡ toLens inner P.∘L toLens outer
comp-preserved : ∀ {A B C : Set}
               → (inner : R.Lens B C) (outer : R.Lens A B)
               → toLens (inner R.∘L outer)
                 ≡ (toLens inner P.∘L toLens outer)
comp-preserved (R.mkLens _ _) (R.mkLens _ _) = refl

-- Identity is preserved
id-preserved : ∀ {A : Set} → toLens (R.idLens {A}) ≡ P.idLens
id-preserved = refl
