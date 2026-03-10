{-# OPTIONS --without-K #-}

-- Css.Show: CSS-safe numeric display
--
-- showFloat produces clean CSS output:
--   showFloat 1.5 → "1.5"
--   showFloat 1.0 → "1"
--   showFloat 1e-7 → "0.0000001"  (no scientific notation)
--
-- JS String() already strips trailing ".0" for integers and trailing
-- zeros for decimals. The COMPILE JS pragma adds handling for the
-- scientific notation case (e.g. 1e-7) which String() does not fix.

module Agdelte.Css.Show where

open import Agda.Builtin.Float using (Float; primShowFloat)
open import Agda.Builtin.String using (String)

showFloat : Float → String
showFloat = primShowFloat

{-# COMPILE JS showFloat = f => { const s = String(f); return s.includes('e') ? f.toFixed(6).replace(/\.?0+$/, '') : s; } #-}
