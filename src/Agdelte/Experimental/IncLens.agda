{-# OPTIONS --without-K --safe #-}

-- EXPERIMENTAL: Incremental Lens (for Widget Lenses)
--
-- Delta type: changes to a position.
-- For now, we use a simple approach: delta is just a new value.
-- In a full implementation, this would be a proper diff type.
--
-- Moved from Agdelte.Theory.Poly (forward-looking, not yet used in runtime).

module Agdelte.Experimental.IncLens where

open import Function using (_∘_; id)
open import Agdelte.Theory.Poly

------------------------------------------------------------------------
-- Incremental Lens
------------------------------------------------------------------------

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
