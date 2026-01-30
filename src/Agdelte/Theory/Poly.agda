{-# OPTIONS --without-K --safe #-}

-- Polynomial Functors - theoretical foundation of Agdelte
-- Based on work by David Spivak and Nelson Niu
-- Poly = ∑(i : Pos) (Dir i → -)
-- MVP version: without universe polymorphism

module Agdelte.Theory.Poly where

open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Function using (_∘_; id)

------------------------------------------------------------------------
-- Polynomial Functor
------------------------------------------------------------------------

-- Polynomial: set of positions (outputs) and directions (inputs) for each position
record Poly : Set₁ where
  constructor mkPoly
  field
    Pos : Set             -- Positions (possible outputs)
    Dir : Pos → Set       -- Directions for each position (inputs)

open Poly public

------------------------------------------------------------------------
-- Interpretation: Poly as functor Set → Set
------------------------------------------------------------------------

-- Applying polynomial to a set
⟦_⟧ : Poly → Set → Set
⟦ P ⟧ X = Σ (Pos P) λ p → Dir P p → X

-- map for functor
mapPoly : (P : Poly) {A B : Set} → (A → B) → ⟦ P ⟧ A → ⟦ P ⟧ B
mapPoly P f (p , k) = p , f ∘ k

------------------------------------------------------------------------
-- Lens: morphism between polynomials
------------------------------------------------------------------------

-- Lens is a pair of functions: forward on positions, backward on directions
record Lens (P Q : Poly) : Set where
  constructor mkLens
  field
    onPos : Pos P → Pos Q
    onDir : (p : Pos P) → Dir Q (onPos p) → Dir P p

open Lens public

-- Identity lens
idLens : {P : Poly} → Lens P P
idLens = mkLens id (λ _ → id)

-- Composition of lenses
_∘L_ : {P Q R : Poly} → Lens Q R → Lens P Q → Lens P R
(mkLens f g) ∘L (mkLens h k) = mkLens (f ∘ h) (λ p → k p ∘ g (h p))

------------------------------------------------------------------------
-- Coalgebra: system with state
------------------------------------------------------------------------

-- Coalgebra of polynomial P is a type with state, implementing interface P
record Coalg (P : Poly) : Set₁ where
  constructor mkCoalg
  field
    State : Set
    observe : State → Pos P                           -- What we output
    update : (s : State) → Dir P (observe s) → State  -- How we update

open Coalg public

------------------------------------------------------------------------
-- Standard polynomials
------------------------------------------------------------------------

-- Identity polynomial: y (one input, one output)
𝕪 : Poly
𝕪 = mkPoly ⊤ (λ _ → ⊤)

-- Constant polynomial: A (only outputs, no inputs)
Const : Set → Poly
Const A = mkPoly A (λ _ → ⊥)

-- Monomial polynomial: A · y^B
Mono : Set → Set → Poly
Mono A B = mkPoly A (λ _ → B)

------------------------------------------------------------------------
-- Monoidal structures
------------------------------------------------------------------------

-- Parallel composition (tensor product): P ⊗ Q
-- (p, q) position, separate directions
_⊗_ : Poly → Poly → Poly
P ⊗ Q = mkPoly
  (Pos P × Pos Q)
  (λ { (p , q) → Dir P p ⊎ Dir Q q })

-- Sum (choice): P ⊕ Q
_⊕_ : Poly → Poly → Poly
P ⊕ Q = mkPoly
  (Pos P ⊎ Pos Q)
  (λ { (inj₁ p) → Dir P p ; (inj₂ q) → Dir Q q })

-- Sequential composition: P ◁ Q
-- Position is a pair (p, function from Dir P p to Pos Q)
-- Direction is a dependent pair
_◁_ : Poly → Poly → Poly
P ◁ Q = mkPoly
  (Σ (Pos P) λ p → Dir P p → Pos Q)
  (λ { (p , f) → Σ (Dir P p) λ d → Dir Q (f d) })

------------------------------------------------------------------------
-- Wiring diagrams (connecting diagrams)
------------------------------------------------------------------------

-- Parallel connection of coalgebras
parallel : {P Q : Poly} → Coalg P → Coalg Q → Coalg (P ⊗ Q)
parallel C D = mkCoalg
  (State C × State D)
  (λ { (s , t) → observe C s , observe D t })
  (λ { (s , t) (inj₁ d) → update C s d , t
     ; (s , t) (inj₂ d) → s , update D t d })

-- Choice between coalgebras
choice : {P Q : Poly} → Coalg P → Coalg Q → Coalg (P ⊕ Q)
choice C D = mkCoalg
  (State C ⊎ State D)
  (λ { (inj₁ s) → inj₁ (observe C s) ; (inj₂ t) → inj₂ (observe D t) })
  (λ { (inj₁ s) d → inj₁ (update C s d) ; (inj₂ t) d → inj₂ (update D t d) })

------------------------------------------------------------------------
-- Utilities
------------------------------------------------------------------------

-- Transforming coalgebra through lens
transformCoalg : {P Q : Poly} → Lens P Q → Coalg P → Coalg Q
transformCoalg (mkLens f g) C = mkCoalg
  (State C)
  (f ∘ observe C)
  (λ s d → update C s (g (observe C s) d))

------------------------------------------------------------------------
-- Incremental Lens (for Widget Lenses)
------------------------------------------------------------------------

-- Delta type: changes to a position
-- For now, we use a simple approach: delta is just a new value
-- In a full implementation, this would be a proper diff type

record IncLens (P Q : Poly) : Set₁ where
  constructor mkIncLens
  field
    -- Standard lens operations
    lens : Lens P Q
    -- Delta type for positions of P
    ΔPos : Pos P → Set
    -- How delta propagates: ΔP p → ΔQ (onPos p)
    -- This is the key: instead of diffing, we propagate deltas through the lens
    onDelta : (p : Pos P) → ΔPos p → Dir Q (Lens.onPos lens p)

open IncLens public

-- Identity incremental lens
idIncLens : {P : Poly} → IncLens P P
idIncLens {P} = mkIncLens idLens (Dir P) (λ p d → d)

-- Composition of incremental lenses
-- Requires a bridge: Dir Q q → ΔPos iq q, so output deltas of ip
-- can feed into input deltas of iq. This holds trivially when
-- ΔPos = Dir (the canonical case, as in idIncLens).
_∘IL_ : {P Q R : Poly}
       → (iq : IncLens Q R) → (ip : IncLens P Q)
       → (∀ q → Dir Q q → ΔPos iq q)
       → IncLens P R
_∘IL_ {P} {Q} {R} iq ip bridge = mkIncLens
  (lens iq ∘L lens ip)
  (ΔPos ip)
  (λ p δp → onDelta iq (Lens.onPos (lens ip) p)
             (bridge (Lens.onPos (lens ip) p) (onDelta ip p δp)))
