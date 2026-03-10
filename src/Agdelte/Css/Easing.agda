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

open import Data.Nat using (ℕ)
open import Data.Nat.Show using (show)
open import Data.Float using (Float)
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
  "cubic-bezier(" ++ showFloat a ++ "," ++ showFloat b ++ ","
                  ++ showFloat c ++ "," ++ showFloat d ++ ")"
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

------------------------------------------------------------------------
-- Easing as Float → Float (for model-driven animations)
------------------------------------------------------------------------

-- Re-exported from Agdelte.Anim.Easing (the canonical location).
open import Agdelte.Anim.Easing public
  using (linearFn; easeInFn; easeOutFn; easeInOutFn)
