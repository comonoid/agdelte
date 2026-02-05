{-# OPTIONS --without-K #-}

-- Css.Length: typed CSS length units
--
-- Produces strings like "16px", "1.5rem", "100%", "0".
-- Used by typed property constructors in Properties.agda.
-- Raw escape hatch: use "prop" ∶ "value" directly.

module Agdelte.Css.Length where

open import Data.Nat using (ℕ)
open import Data.Nat.Show using (show)
open import Data.Float using (Float)
open import Data.String using (String; _++_)

open import Agdelte.Css.Show using (showFloat)

------------------------------------------------------------------------
-- Length
------------------------------------------------------------------------

data Length : Set where
  px   : ℕ → Length
  rem  : Float → Length
  em   : Float → Length
  pct  : Float → Length      -- percent
  vh   : Float → Length
  vw   : Float → Length
  zero : Length

showLength : Length → String
showLength (px n)  = show n ++ "px"
showLength (rem f) = showFloat f ++ "rem"
showLength (em f)  = showFloat f ++ "em"
showLength (pct f) = showFloat f ++ "%"
showLength (vh f)  = showFloat f ++ "vh"
showLength (vw f)  = showFloat f ++ "vw"
showLength zero    = "0"
