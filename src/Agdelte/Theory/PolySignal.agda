{-# OPTIONS --without-K --guardedness #-}

-- PolySignal: explicit connection between Signal and Polynomial Functors
-- Demonstrates that Signal A ≅ Coalg (Mono A ⊤)

module Agdelte.Theory.PolySignal where

open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Function using (_∘_; id)

open import Agdelte.Theory.Poly
open import Agdelte.Core.Signal

private
  variable
    A B : Set

------------------------------------------------------------------------
-- Signal as coalgebra of polynomial Mono A ⊤
------------------------------------------------------------------------

-- Polynomial for Signal A
-- Pos = A (observable value)
-- Dir = λ _ → ⊤ (trivial input for transition)
SignalPoly : Set → Poly
SignalPoly A = Mono A ⊤

-- Check: interpretation of SignalPoly gives A × X
-- ⟦SignalPoly A⟧ X = Σ A (λ _ → ⊤ → X) ≅ A × X

------------------------------------------------------------------------
-- Converting Signal to Coalg
------------------------------------------------------------------------

-- Signal A can be viewed as coalgebra SignalPoly A
-- where State = Signal A
signalToCoalg : ∀ {A} → Coalg (SignalPoly A)
signalToCoalg {A} = mkCoalg
  (Signal A)           -- State
  now                  -- observe : Signal A → A
  (λ s _ → next s)     -- update  : Signal A → ⊤ → Signal A

------------------------------------------------------------------------
-- Operations on Signal through Poly
------------------------------------------------------------------------

-- map for Signal through mapPoly
-- This shows that mapS corresponds to functoriality of polynomial
mapS-via-Poly : ∀ {A B : Set} → (A → B) → Signal A → Signal B
mapS-via-Poly {A} {B} f s = go s
  where
    go : Signal A → Signal B
    now  (go s') = f (now s')
    next (go s') = go (next s')

-- Lens between SignalPoly A and SignalPoly B induced by function A → B
signalLens : (A → B) → Lens (SignalPoly A) (SignalPoly B)
signalLens f = mkLens f (λ _ _ → tt)

------------------------------------------------------------------------
-- Constant signal as coalgebra
------------------------------------------------------------------------

-- Constant signal is a coalgebra with single-point state
constSignalCoalg : A → Coalg (SignalPoly A)
constSignalCoalg a = mkCoalg
  ⊤                    -- State = ⊤ (one state)
  (λ _ → a)            -- observe : ⊤ → A
  (λ _ _ → tt)         -- update  : ⊤ → ⊤ → ⊤

-- Unfolding coalgebra into Signal
unfoldSignal : ∀ {S : Set} {A : Set} → (S → A) → (S → S) → S → Signal A
now  (unfoldSignal {S} {A} obs step s) = obs s
next (unfoldSignal {S} {A} obs step s) = unfoldSignal {S} {A} obs step (step s)

-- Any coalgebra SignalPoly A unfolds into Signal A
coalgToSignal : ∀ {A} → (c : Coalg (SignalPoly A)) → State c → Signal A
coalgToSignal {A} c s₀ = unfoldSignal {State c} {A} (observe c) (λ s → update c s tt) s₀

------------------------------------------------------------------------
-- Isomorphism between Signal and Coalg (informally)
------------------------------------------------------------------------

-- Formally, Signal A and Coalg (SignalPoly A) with State = Signal A
-- form equivalent structures. Functions now/next directly
-- correspond to observe/update.

-- Signal → Coalg → Signal should give original signal:
-- coalgToSignal signalToCoalg s ≡ s  (requires bisimilarity)

