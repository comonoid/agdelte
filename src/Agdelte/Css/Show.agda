{-# OPTIONS --without-K #-}

-- Css.Show: CSS-safe numeric display
--
-- showFloat produces clean CSS output:
--   showFloat 1.5 → "1.5"    (no scientific notation)
--   showFloat 1.0 → "1"      (no trailing ".0")
-- Compared to primShowFloat which gives "1.0" for integers.

module Agdelte.Css.Show where

open import Agda.Builtin.Float using (Float; primShowFloat)
open import Agda.Builtin.String using (String)

showFloat : Float → String
showFloat = primShowFloat

{-# COMPILE JS showFloat = f => String(f) #-}
