{-# OPTIONS --without-K #-}

-- Css.Layout: flexbox and grid convenience styles
--
-- Each helper returns Style, composable via _<>_:
--   div (toAttrs (row <> center <> gap' (px 12) ∷ []))

module Agdelte.Css.Layout where

open import Data.List using ([]; _∷_)
open import Data.String using (String)

open import Agdelte.Css.Decl using (Style; Decl; _∶_; _<>_)
open import Agdelte.Css.Length using (Length)
open import Agdelte.Css.Properties using (gap')

------------------------------------------------------------------------
-- Flexbox
------------------------------------------------------------------------

row : Style
row = "display" ∶ "flex" ∷ "flex-direction" ∶ "row" ∷ []

col : Style
col = "display" ∶ "flex" ∷ "flex-direction" ∶ "column" ∷ []

-- Flex centering (includes display: flex; idempotent when combined with row/col)
center : Style
center = "display" ∶ "flex" ∷ "justify-content" ∶ "center" ∷ "align-items" ∶ "center" ∷ []

-- Flex space-between (includes display: flex; idempotent when combined with row/col)
spaceBetween : Style
spaceBetween = "display" ∶ "flex" ∷ "justify-content" ∶ "space-between" ∷ "align-items" ∶ "center" ∷ []

wrap : Style
wrap = "flex-wrap" ∶ "wrap" ∷ []

------------------------------------------------------------------------
-- Grid
------------------------------------------------------------------------

grid : String → Style
grid cols = "display" ∶ "grid" ∷ "grid-template-columns" ∶ cols ∷ []

------------------------------------------------------------------------
-- Common patterns
------------------------------------------------------------------------

-- Vertical stack with gap
stack : Length → Style
stack g = col <> (gap' g ∷ [])

-- Horizontal row with gap
inline : Length → Style
inline g = row <> (gap' g ∷ [])
