{-# OPTIONS --without-K #-}

-- CSS styles for the Checkbox control
-- (HTML structure is in Agdelte.Html.Controls.Checkbox)

module Agdelte.Css.Controls.Checkbox where

open import Data.List using (List; []; _∷_)

open import Agdelte.Css.Decl using (Style; _∶_)
open import Agdelte.Css.Stylesheet using (Rule; rule; Stylesheet)

------------------------------------------------------------------------
-- Checkbox rules
------------------------------------------------------------------------

checkboxRules : Stylesheet
checkboxRules =
    rule ".agdelte-checkbox"
      ( "display" ∶ "flex"
      ∷ "align-items" ∶ "center"
      ∷ "gap" ∶ "var(--agdelte-spacing-sm)"
      ∷ "cursor" ∶ "pointer"
      ∷ "padding" ∶ "var(--agdelte-spacing-xs) 0"
      ∷ [])
  ∷ rule ".agdelte-checkbox__input"
      ( "width" ∶ "18px"
      ∷ "height" ∶ "18px"
      ∷ "margin" ∶ "0"
      ∷ "cursor" ∶ "pointer"
      ∷ "accent-color" ∶ "var(--agdelte-primary)"
      ∷ [])
  ∷ rule ".agdelte-checkbox__label"
      ( "color" ∶ "var(--agdelte-text)"
      ∷ "user-select" ∶ "none"
      ∷ [])
  ∷ rule ".agdelte-checkbox-group"
      ( "display" ∶ "flex"
      ∷ "flex-direction" ∶ "column"
      ∷ "gap" ∶ "var(--agdelte-spacing-xs)"
      ∷ [])
  ∷ rule ".agdelte-checkbox-group--inline"
      ( "flex-direction" ∶ "row"
      ∷ "flex-wrap" ∶ "wrap"
      ∷ "gap" ∶ "var(--agdelte-spacing-md)"
      ∷ [])
  ∷ []
