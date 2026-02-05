{-# OPTIONS --without-K #-}

-- Css.Color: typed CSS color values
--
-- Type-safe color constructors: hex, rgb, rgba, hsl, named, var.
-- Raw escape hatch: raw "any-css-color-expression".

module Agdelte.Css.Color where

open import Data.Nat using (ℕ)
open import Data.Nat.Show using (show)
open import Data.Float using (Float)
open import Data.String using (String; _++_)

open import Agdelte.Css.Show using (showFloat)

------------------------------------------------------------------------
-- Color
------------------------------------------------------------------------

data Color : Set where
  hex   : String → Color              -- "#ff0000"
  rgb   : ℕ → ℕ → ℕ → Color
  rgba  : ℕ → ℕ → ℕ → Float → Color
  hsl   : ℕ → ℕ → ℕ → Color
  named : String → Color              -- "red", "transparent"
  var   : String → Color              -- CSS custom property
  raw   : String → Color              -- escape hatch

showColor : Color → String
showColor (hex s)        = s
showColor (rgb r g b)    = "rgb(" ++ show r ++ "," ++ show g ++ "," ++ show b ++ ")"
showColor (rgba r g b a) = "rgba(" ++ show r ++ "," ++ show g ++ "," ++ show b ++ "," ++ showFloat a ++ ")"
showColor (hsl h s l)    = "hsl(" ++ show h ++ "," ++ show s ++ "%," ++ show l ++ "%)"
showColor (named s)      = s
showColor (var s)        = "var(--" ++ s ++ ")"
showColor (raw s)        = s
