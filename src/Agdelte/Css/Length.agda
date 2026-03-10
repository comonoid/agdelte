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
  pxf  : Float → Length     -- fractional / negative pixel values
  rem  : Float → Length
  em   : Float → Length
  ch   : Float → Length
  pct  : Float → Length      -- percent
  vh   : Float → Length
  vw   : Float → Length
  svh  : Float → Length      -- small viewport height
  svw  : Float → Length      -- small viewport width
  dvh  : Float → Length      -- dynamic viewport height
  dvw  : Float → Length      -- dynamic viewport width
  cqw  : Float → Length      -- container query width
  cqh  : Float → Length      -- container query height
  zero : Length
  auto : Length

showLength : Length → String
showLength (px n)   = show n ++ "px"
showLength (pxf f)  = showFloat f ++ "px"
showLength (rem f)  = showFloat f ++ "rem"
showLength (em f)  = showFloat f ++ "em"
showLength (ch f)  = showFloat f ++ "ch"
showLength (pct f) = showFloat f ++ "%"
showLength (vh f)  = showFloat f ++ "vh"
showLength (vw f)  = showFloat f ++ "vw"
showLength (svh f) = showFloat f ++ "svh"
showLength (svw f) = showFloat f ++ "svw"
showLength (dvh f) = showFloat f ++ "dvh"
showLength (dvw f) = showFloat f ++ "dvw"
showLength (cqw f) = showFloat f ++ "cqw"
showLength (cqh f) = showFloat f ++ "cqh"
showLength zero    = "0"
showLength auto    = "auto"
