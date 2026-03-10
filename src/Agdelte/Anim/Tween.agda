{-# OPTIONS --without-K #-}

-- Anim.Tween: model-driven tween animation
--
-- A Tween interpolates from A to B over time, with easing.
-- It is a coalgebra of p(y) = A × y^ℕ — the same polynomial as Agent.
--
-- Usage:
--   let t = mkTween 0 300 0.0 1.0 easeOutFn floatLerp
--       (t' , val) = tickTween t 16
--   -- val is the current interpolated value
--   -- t' has elapsed advanced by 16ms

module Agdelte.Anim.Tween where

open import Data.Nat using (ℕ; zero; suc; _+_; _⊓_)
open import Data.Bool using (Bool; not)
open import Data.Product using (_×_; _,_)

import Data.Float as F
import Data.Float.Base as FB

open import Agdelte.Css.Easing using (linearFn; easeInFn; easeOutFn; easeInOutFn)

------------------------------------------------------------------------
-- Tween
------------------------------------------------------------------------

record Tween (A : Set) : Set where
  constructor mkTween
  field
    elapsed  : ℕ           -- ms elapsed so far
    duration : ℕ           -- total ms
    from     : A
    to       : A
    easing   : F.Float → F.Float   -- progress curve [0,1] → [0,1]
    lerp     : A → A → F.Float → A  -- interpolation function

------------------------------------------------------------------------
-- Tick
------------------------------------------------------------------------

tickTween : ∀ {A} → Tween A → ℕ → Tween A × A
tickTween t dt with Tween.duration t
... | zero =
  -- duration=0: immediately at target value (avoid division by zero)
  mkTween 0 0 (Tween.from t) (Tween.to t)
           (Tween.easing t) (Tween.lerp t) , Tween.to t
... | dur@(suc _) =
  let e' = (Tween.elapsed t + dt) ⊓ dur
      progress = Tween.easing t (FB.fromℕ e' F.÷ FB.fromℕ dur)
      value = Tween.lerp t (Tween.from t) (Tween.to t) progress
  in mkTween e' dur (Tween.from t) (Tween.to t)
             (Tween.easing t) (Tween.lerp t) , value

------------------------------------------------------------------------
-- Query
------------------------------------------------------------------------

isComplete : ∀ {A} → Tween A → Bool
isComplete t = not (Tween.elapsed t Data.Nat.<ᵇ Tween.duration t)
  where open import Data.Nat using (_<ᵇ_)

-- Current value without advancing time
currentValue : ∀ {A} → Tween A → A
currentValue t with Tween.duration t
... | zero = Tween.to t
... | dur@(suc _) =
  let progress = Tween.easing t (FB.fromℕ (Tween.elapsed t) F.÷ FB.fromℕ dur)
  in Tween.lerp t (Tween.from t) (Tween.to t) progress

------------------------------------------------------------------------
-- Retarget (interrupt mid-flight)
------------------------------------------------------------------------

-- Capture current interpolated value as new start, reset elapsed to 0.
-- Spring handles interruption naturally (velocity carries over);
-- Tween needs this explicit "snapshot current + restart" step.
retargetTween : ∀ {A} → A → Tween A → Tween A
retargetTween newTo t =
  mkTween 0 (Tween.duration t) (currentValue t) newTo
          (Tween.easing t) (Tween.lerp t)

------------------------------------------------------------------------
-- Common interpolation functions
------------------------------------------------------------------------

floatLerp : F.Float → F.Float → F.Float → F.Float
floatLerp a b t = a F.+ (b F.- a) F.* t
