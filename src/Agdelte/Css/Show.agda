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
--
-- Known limits of toFixed(6):
--   Values < 1e-6 round to "0"  (e.g. 1e-8 → "0")
--   Values >= 1e21 pass through as scientific notation ("1e+21")
-- Both are non-issues for CSS (sub-pixel precision / astronomical values).

module Agdelte.Css.Show where

open import Data.Float.Base using (Float) renaming (show to showFloat′)
open import Data.String using (String)

showFloat : Float → String
showFloat = showFloat′

{-# COMPILE JS showFloat = f => { if (!isFinite(f)) return "0"; const s = String(f); return s.includes('e') ? f.toFixed(6).replace(/\.?0+$/, '') : s; } #-}

-- GHC backend: use showFFloat to avoid scientific notation in CSS output.
-- Haskell's `show` produces "1.0e-7" which is invalid CSS; showFFloat
-- produces "0.0000001". For sub-pixel values < 1e-6, rounds to "0".
{-# FOREIGN GHC import Numeric (showFFloat) #-}
{-# FOREIGN GHC import qualified Data.Text #-}
{-# COMPILE GHC showFloat = \f -> Data.Text.pack (showFFloat Nothing f "") #-}
