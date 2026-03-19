{-# OPTIONS --without-K #-}

-- Css.Easing: CSS easing functions and duration types
--
-- Shared between CSS transitions/animations and
-- model-driven animations.
--
-- CSS usage:
--   transition' (trans "opacity" (ms 300) ease ∷ [])
--
-- Model usage:
--   mkTween { easing = easeOutFn; ... }

module Agdelte.Css.Easing where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show using (show)
open import Data.Float using (Float; _≡ᵇ_; _<ᵇ_)
open import Data.Bool using (if_then_else_)
open import Data.String using (String; _++_)

open import Agdelte.Css.Show using (showFloat)

------------------------------------------------------------------------
-- Easing (CSS keyword)
------------------------------------------------------------------------

data Easing : Set where
  ease linear easeIn easeOut easeInOut : Easing
  cubicBezier : Float → Float → Float → Float → Easing
  raw         : String → Easing

showEasing : Easing → String
showEasing ease       = "ease"
showEasing linear     = "linear"
showEasing easeIn     = "ease-in"
showEasing easeOut    = "ease-out"
showEasing easeInOut  = "ease-in-out"
showEasing (cubicBezier a b c d) =
  let clamp : Float → Float
      clamp x = if x <ᵇ 0.0 then 0.0 else (if 1.0 <ᵇ x then 1.0 else x)
  in "cubic-bezier(" ++ showFloat (clamp a) ++ ", " ++ showFloat b ++ ", "
                      ++ showFloat (clamp c) ++ ", " ++ showFloat d ++ ")"
showEasing (raw s) = s

------------------------------------------------------------------------
-- Duration
------------------------------------------------------------------------

data Duration : Set where
  ms : ℕ → Duration
  s  : Float → Duration

showDuration : Duration → String
showDuration (ms n) = show n ++ "ms"
showDuration (s f)  = showFloat f ++ "s"

-- | Render an optional delay suffix for transition/animation shorthand.
-- Zero delay (both `ms 0` and `s 0.0`) is omitted for cleaner output.
-- NB: Float._≡ᵇ_ treats -0.0 ≡ᵇ 0.0 = true in JS (Object.is is not used),
-- and NaN ≡ᵇ NaN = false. CSS delays are non-negative and finite, so this is safe.
renderDelay : Duration → String
renderDelay (ms zero)    = ""
renderDelay (ms (suc n)) = " " ++ showDuration (ms (suc n))
renderDelay (s f)        = if f ≡ᵇ 0.0 then "" else " " ++ showDuration (s f)

------------------------------------------------------------------------
-- Easing as Float → Float (for model-driven animations)
------------------------------------------------------------------------

-- Re-exported from Agdelte.Anim.Easing (the canonical location).
open import Agdelte.Anim.Easing public
  using (linearFn; easeInFn; easeOutFn; easeInOutFn)
