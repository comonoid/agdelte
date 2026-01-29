{-# OPTIONS --without-K --guardedness #-}

-- Signal: discrete stream of values (coinductive)
-- Signal A ≅ Coalg (Mono A ⊤) = ν X. A × X
--
-- Polynomial Mono A ⊤ has:
--   Pos = A (what we output)
--   Dir = λ _ → ⊤ (one input for transition to next)
--
-- Interpretation: ⟦Mono A ⊤⟧(X) = Σ A (λ _ → ⊤ → X) ≅ A × X

module Agdelte.Core.Signal where

open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; map; concat; filter; foldr)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Maybe using (Maybe; just; nothing)
open import Function using (_∘_; id; const)

private
  variable
    A B C : Set

------------------------------------------------------------------------
-- Signal: coinductive discrete stream
------------------------------------------------------------------------

record Signal (A : Set) : Set where
  coinductive
  field
    now  : A           -- Current value
    next : Signal A    -- Next time step

open Signal public

------------------------------------------------------------------------
-- Constructors
------------------------------------------------------------------------

-- Constant signal
constant : A → Signal A
now  (constant a) = a
next (constant a) = constant a

-- Synonym for clarity
pure : A → Signal A
pure = constant

------------------------------------------------------------------------
-- Functor
------------------------------------------------------------------------

-- map for Signal (lazy)
mapS : (A → B) → Signal A → Signal B
now  (mapS f s) = f (now s)
next (mapS f s) = mapS f (next s)

-- Infix version
_<$>_ : (A → B) → Signal A → Signal B
_<$>_ = mapS

infixl 4 _<$>_

------------------------------------------------------------------------
-- Applicative
------------------------------------------------------------------------

-- Applying function from signal to value from signal
_<*>_ : Signal (A → B) → Signal A → Signal B
now  (sf <*> sa) = now sf (now sa)
next (sf <*> sa) = next sf <*> next sa

infixl 4 _<*>_

-- liftA2
liftA2 : (A → B → C) → Signal A → Signal B → Signal C
liftA2 f sa sb = mapS f sa <*> sb

-- liftA3
liftA3 : ∀ {D : Set} → (A → B → C → D) → Signal A → Signal B → Signal C → Signal D
liftA3 f sa sb sc = liftA2 f sa sb <*> sc

------------------------------------------------------------------------
-- Temporal combinators
------------------------------------------------------------------------

-- Delay by one tick (pre with initial value)
pre : A → Signal A → Signal A
now  (pre a s) = a
next (pre a s) = pre (now s) (next s)

-- Shift backward (delay)
delay : A → Signal A → Signal A
delay = pre

-- Zip two signals
zipS : Signal A → Signal B → Signal (A × B)
zipS sa sb = liftA2 _,_ sa sb

-- Scan (foldl through time)
scanS : (B → A → B) → B → Signal A → Signal B
now  (scanS f b s) = b
next (scanS f b s) = scanS f (f b (now s)) (next s)

------------------------------------------------------------------------
-- Sampling values
------------------------------------------------------------------------

-- Take n values from signal (for debugging)
takeS : ℕ → Signal A → List A
takeS zero    s = []
takeS (suc n) s = now s ∷ takeS n (next s)

-- Skip n values
dropS : ℕ → Signal A → Signal A
dropS zero    s = s
dropS (suc n) s = dropS n (next s)

------------------------------------------------------------------------
-- Combining
------------------------------------------------------------------------

-- Choose between two signals by condition
switch : Signal Bool → Signal A → Signal A → Signal A
now  (switch c t f) = if now c then now t else now f
next (switch c t f) = switch (next c) (next t) (next f)

-- Merge with preference for first
merge : Signal (Maybe A) → Signal (Maybe A) → Signal (Maybe A)
now (merge s₁ s₂) with now s₁
... | just a  = just a
... | nothing = now s₂
next (merge s₁ s₂) = merge (next s₁) (next s₂)

------------------------------------------------------------------------
-- Integration with polynomials
------------------------------------------------------------------------

-- Signal A as coalgebra of polynomial Mono A ⊤:
--   State   = Signal A
--   observe = now  : Signal A → A
--   update  = λ s _ → next s : Signal A → ⊤ → Signal A
--
-- The record Signal structure directly implements this coalgebra:
--   now  corresponds to observe
--   next corresponds to update (with trivial argument ⊤)

------------------------------------------------------------------------
-- Utilities
------------------------------------------------------------------------

-- Indexing by time
_!!_ : Signal A → ℕ → A
s !! zero    = now s
s !! suc n   = next s !! n

infixl 9 _!!_

-- Comparing with previous value
changed : {A : Set} → (A → A → Bool) → Signal A → Signal Bool
now  (changed eq s) = false  -- At first moment there is no previous
next (changed eq s) = changed' eq (now s) (next s)
  where
    changed' : (A → A → Bool) → A → Signal A → Signal Bool
    now  (changed' eq prev s) = if eq prev (now s) then false else true
    next (changed' eq prev s) = changed' eq (now s) (next s)

-- Creating a counter (call with initial value)
-- Note: we don't define global counter, since JS backend
-- evaluates it immediately (eager), which causes infinite recursion.
-- Use: mkCounter 0 where you need a counter.
mkCounter : ℕ → Signal ℕ
now  (mkCounter n) = n
next (mkCounter n) = mkCounter (suc n)
