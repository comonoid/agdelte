{-# OPTIONS --without-K #-}

-- Proof: TotalOptic ≅ Poly.Lens for the monomial case
--
-- Optic.peek returns Maybe A, so the general Optic cannot correspond
-- directly to Poly.Lens (which is total). We introduce TotalOptic,
-- the subtype where peek is total (S → A), and prove:
--
--   TotalOptic S A  ≅  Poly.Lens (Mono S S) (Mono A A)
--
-- Additionally, every Reactive.Lens-constructed Optic (via fromLens)
-- factors through TotalOptic, closing the connection to the existing
-- Reactive.Lens ≅ Poly.Lens proof in OpticPolyLens.agda.

module Agdelte.Theory.OpticPolyOptic where

open import Data.Maybe using (Maybe; just; nothing)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Agdelte.Reactive.Optic  as O
import Agdelte.Reactive.Lens   as R
import Agdelte.Theory.Poly     as P

------------------------------------------------------------------------
-- TotalOptic: the subtype of Optic where peek is total
--
-- Fields are peek/set (not peek/over) so the representation matches
-- Poly.Lens (onPos/onDir) and the isomorphism holds definitionally.
-- over is derived as a convenience.
------------------------------------------------------------------------

record TotalOptic (S A : Set) : Set where
  constructor mkTotalOptic
  field
    peek : S → A
    set  : A → S → S

  over : (A → A) → S → S
  over f s = set (f (peek s)) s

open TotalOptic public

------------------------------------------------------------------------
-- Forward: TotalOptic → Poly.Lens (Mono S S) (Mono A A)
------------------------------------------------------------------------

toPolyLens : ∀ {S A : Set}
           → TotalOptic S A
           → P.Lens (P.Mono S S) (P.Mono A A)
toPolyLens t = P.mkLens (peek t) (λ s a → set t a s)

------------------------------------------------------------------------
-- Backward: Poly.Lens (Mono S S) (Mono A A) → TotalOptic
------------------------------------------------------------------------

fromPolyLens : ∀ {S A : Set}
             → P.Lens (P.Mono S S) (P.Mono A A)
             → TotalOptic S A
fromPolyLens pl = mkTotalOptic (P.onPos pl) (λ a s → P.onDir pl s a)

------------------------------------------------------------------------
-- Round-trip proofs
------------------------------------------------------------------------

-- fromPolyLens (toPolyLens t) ≡ t
from∘to : ∀ {S A : Set} (t : TotalOptic S A)
        → fromPolyLens (toPolyLens t) ≡ t
from∘to (mkTotalOptic _ _) = refl

-- toPolyLens (fromPolyLens pl) ≡ pl
to∘from : ∀ {S A : Set} (pl : P.Lens (P.Mono S S) (P.Mono A A))
        → toPolyLens (fromPolyLens pl) ≡ pl
to∘from (P.mkLens _ _) = refl

------------------------------------------------------------------------
-- Embedding: TotalOptic → Optic (via just)
------------------------------------------------------------------------

embed : ∀ {S A : Set} → TotalOptic S A → O.Optic S A
embed t = O.mkOptic (just ∘ peek t) (over t)

------------------------------------------------------------------------
-- fromLens factors through TotalOptic
--
-- Reactive.Lens l  ──fromLens──▶  Optic
--       │                            ▲
--       └──fromLensTotal──▶ TotalOptic ──embed──┘
------------------------------------------------------------------------

fromLensTotal : ∀ {S A : Set} → R.Lens S A → TotalOptic S A
fromLensTotal l = mkTotalOptic (R.get l) (R.set l)

-- embed (fromLensTotal l) ≡ fromLens l
embed∘fromLensTotal : ∀ {S A : Set} (l : R.Lens S A)
                    → embed (fromLensTotal l) ≡ O.fromLens l
embed∘fromLensTotal (R.mkLens _ _) = refl

------------------------------------------------------------------------
-- Composition is preserved
------------------------------------------------------------------------

-- TotalOptic composition
_∘T_ : ∀ {A B C : Set} → TotalOptic B C → TotalOptic A B → TotalOptic A C
inner ∘T outer = mkTotalOptic
  (peek inner ∘ peek outer)
  (λ c a → set outer (set inner c (peek outer a)) a)

infixr 9 _∘T_

-- Identity TotalOptic
idTotalOptic : ∀ {A : Set} → TotalOptic A A
idTotalOptic = mkTotalOptic id (λ a _ → a)

-- toPolyLens (inner ∘T outer) ≡ toPolyLens inner P.∘L toPolyLens outer
comp-preserved : ∀ {A B C : Set}
               → (inner : TotalOptic B C) (outer : TotalOptic A B)
               → toPolyLens (inner ∘T outer)
                 ≡ (toPolyLens inner P.∘L toPolyLens outer)
comp-preserved (mkTotalOptic _ _) (mkTotalOptic _ _) = refl

-- Identity is preserved
id-preserved : ∀ {A : Set} → toPolyLens (idTotalOptic {A}) ≡ P.idLens
id-preserved = refl
