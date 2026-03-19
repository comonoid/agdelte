{-# OPTIONS --without-K #-}

-- CSS styles for the RadioGroup control
-- (HTML structure is in Agdelte.Html.Controls.RadioGroup)

module Agdelte.Css.Controls.RadioGroup where

open import Data.List using (List; []; _∷_)

open import Agdelte.Css.Decl using (Style; _∶_; focusOutline; cursorPointer)
open import Agdelte.Css.Stylesheet using (Rule; rule; Stylesheet)

------------------------------------------------------------------------
-- RadioGroup rules
------------------------------------------------------------------------

radioGroupRules : Stylesheet
radioGroupRules =
    rule ".agdelte-radio"
      ( "display" ∶ "flex"
      ∷ "align-items" ∶ "center"
      ∷ "gap" ∶ "var(--agdelte-spacing-sm)"
      ∷ cursorPointer
      ∷ "padding" ∶ "var(--agdelte-spacing-xs) 0"
      ∷ [])
  ∷ rule ".agdelte-radio__input"
      ( "width" ∶ "18px"
      ∷ "height" ∶ "18px"
      ∷ "margin" ∶ "0"
      ∷ cursorPointer
      ∷ "accent-color" ∶ "var(--agdelte-primary)"
      ∷ [])
  ∷ rule ".agdelte-radio__input:focus-visible"
      focusOutline
  ∷ rule ".agdelte-radio__label"
      ( "color" ∶ "var(--agdelte-text)"
      ∷ "user-select" ∶ "none"
      ∷ [])
  ∷ rule ".agdelte-radio-group"
      ( "display" ∶ "flex"
      ∷ "flex-direction" ∶ "column"
      ∷ "gap" ∶ "var(--agdelte-spacing-xs)"
      ∷ [])
  ∷ rule ".agdelte-radio-group--inline"
      ( "flex-direction" ∶ "row"
      ∷ "flex-wrap" ∶ "wrap"
      ∷ "gap" ∶ "var(--agdelte-spacing-md)"
      ∷ [])
  ∷ []
