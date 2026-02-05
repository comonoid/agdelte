{-# OPTIONS --without-K #-}

-- Css.Conditional: compile-time conditional styles
--
-- For styles that depend on a Bool known at template construction:
--   toAttrs (baseStyle <> styleIf isActive activeHighlight)
--
-- For model-dependent dynamic styles, use styleBind instead.

module Agdelte.Css.Conditional where

open import Data.Bool using (Bool; true; false)

open import Agdelte.Css.Decl using (Style; none)

------------------------------------------------------------------------
-- Conditional styles
------------------------------------------------------------------------

-- Include style when condition is true, empty otherwise
styleIf : Bool → Style → Style
styleIf true  s = s
styleIf false _ = none

-- Choose between two styles based on condition
styleWhen : Bool → Style → Style → Style
styleWhen true  active _       = active
styleWhen false _      fallback = fallback
