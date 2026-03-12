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

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false; if_then_else_)

open import Agdelte.Css.Show using (showFloat)

------------------------------------------------------------------------
-- Color
------------------------------------------------------------------------

-- NOTE: No range-checking on constructor arguments. Out-of-range values
-- produce technically invalid CSS that browsers clamp silently:
--   rgba alpha: should be [0,1]; NaN/Infinity produce broken CSS (see Show.agda guard)
--   hsl h: [0,360], s/l: [0,100]; out-of-range values are browser-clamped
--   rgb r/g/b: [0,255]
-- Use hexValid for validated hex colors.
data Color : Set where
  hex   : String → Color              -- "#ff0000"
  rgb   : ℕ → ℕ → ℕ → Color
  rgba  : ℕ → ℕ → ℕ → Float → Color
  hsl   : ℕ → ℕ → ℕ → Color
  named : String → Color              -- "red", "transparent"
  var   : String → Color              -- CSS custom property
  raw   : String → Color              -- escape hatch

-- Validated hex color constructor: checks format (#RGB, #RRGGBB, #RRGGBBAA)
postulate
  isHexColor : String → Bool

{-# COMPILE JS isHexColor = function(s) {
  return /^#([0-9a-fA-F]{3}|[0-9a-fA-F]{6}|[0-9a-fA-F]{8})$/.test(s)
    ? (cases) => cases["true"]()
    : (cases) => cases["false"]();
} #-}

{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# FOREIGN GHC import Data.Char (isHexDigit) #-}
{-# COMPILE GHC isHexColor = \s ->
  let t = T.unpack s
      validLen xs = let n = length xs in n == 3 || n == 6 || n == 8
  in case t of
       '#':rest -> if validLen rest && all isHexDigit rest
                   then True else False
       _ -> False #-}

hexValid : String → Maybe Color
hexValid s = if isHexColor s then just (hex s) else nothing

showColor : Color → String
showColor (hex s)        = s
showColor (rgb r g b)    = "rgb(" ++ show r ++ ", " ++ show g ++ ", " ++ show b ++ ")"
showColor (rgba r g b a) = "rgba(" ++ show r ++ ", " ++ show g ++ ", " ++ show b ++ ", " ++ showFloat a ++ ")"
showColor (hsl h s l)    = "hsl(" ++ show h ++ ", " ++ show s ++ "%, " ++ show l ++ "%)"
showColor (named s)      = s
showColor (var s)        = "var(--" ++ s ++ ")"
showColor (raw s)        = s
