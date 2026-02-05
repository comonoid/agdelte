{-# OPTIONS --without-K #-}

-- Css.Layout: flexbox and grid convenience styles
--
-- Each helper returns Style, composable via _<>_:
--   div (toAttrs (row <> center <> gap' (px 12) ∷ []))

module Agdelte.Css.Layout where

open import Data.List using ([]; _∷_)
open import Data.String using (String)

open import Agdelte.Css.Decl using (Style; Decl; _∶_; _<>_; singleton)
open import Agdelte.Css.Length using (Length; showLength)

------------------------------------------------------------------------
-- Flexbox
------------------------------------------------------------------------

row : Style
row = "display" ∶ "flex" ∷ "flex-direction" ∶ "row" ∷ []

col : Style
col = "display" ∶ "flex" ∷ "flex-direction" ∶ "column" ∷ []

center : Style
center = "justify-content" ∶ "center" ∷ "align-items" ∶ "center" ∷ []

spaceBetween : Style
spaceBetween = "justify-content" ∶ "space-between" ∷ []

wrap : Style
wrap = "flex-wrap" ∶ "wrap" ∷ []

------------------------------------------------------------------------
-- Grid
------------------------------------------------------------------------

grid : String → Style
grid template = "display" ∶ "grid" ∷ "grid-template" ∶ template ∷ []

------------------------------------------------------------------------
-- Common patterns
------------------------------------------------------------------------

-- Vertical stack with gap
stack : Length → Style
stack g = col <> ("gap" ∶ showLength g ∷ [])

-- Horizontal row with gap
inline : Length → Style
inline g = row <> ("gap" ∶ showLength g ∷ [])
