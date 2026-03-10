{-# OPTIONS --without-K #-}

-- Anim.Easing: easing functions as Float → Float
--
-- Polynomial approximations of common easing curves.
-- Input t ∈ [0, 1], output is the eased progress.
--
-- Used by both Anim.Tween (model-driven) and Css.Easing (CSS transitions).

module Agdelte.Anim.Easing where

open import Data.Float using (Float; _+_; _-_; _*_; _<ᵇ_)
open import Data.Bool using (if_then_else_)

linearFn : Float → Float
linearFn t = t

easeInFn : Float → Float
easeInFn t = t * t * t

easeOutFn : Float → Float
easeOutFn t = let t' = 1.0 - t in 1.0 - t' * t' * t'

easeInOutFn : Float → Float
easeInOutFn t =
  if t <ᵇ 0.5
  then 4.0 * t * t * t
  else 1.0 - (let p = (-2.0) * t + 2.0 in p * p * p) * 0.5
