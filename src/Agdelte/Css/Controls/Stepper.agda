{-# OPTIONS --without-K #-}

-- CSS styles for the Stepper control
-- (HTML structure is in Agdelte.Html.Controls.Stepper)

module Agdelte.Css.Controls.Stepper where

open import Data.List using (List; []; _∷_)

open import Agdelte.Css.Decl using (Style; _∶_; borderRadius; focusOutline; transitionAll; transitionBg; cursorPointer)
open import Agdelte.Css.Stylesheet using (Rule; rule; Stylesheet)

------------------------------------------------------------------------
-- Stepper rules
------------------------------------------------------------------------

stepperRules : Stylesheet
stepperRules =
    rule ".agdelte-stepper"
      ( "display" ∶ "flex"
      ∷ "align-items" ∶ "flex-start"
      ∷ [])
  ∷ rule ".agdelte-stepper--vertical"
      ( "flex-direction" ∶ "column"
      ∷ [])
  ∷ rule ".agdelte-stepper__step"
      ( "display" ∶ "flex"
      ∷ "align-items" ∶ "flex-start"
      ∷ "flex" ∶ "1"
      ∷ "position" ∶ "relative"
      ∷ [])
  ∷ rule ".agdelte-stepper--vertical .agdelte-stepper__step"
      ( "flex" ∶ "none"
      ∷ "margin-bottom" ∶ "var(--agdelte-spacing-md)"
      ∷ [])
  ∷ rule ".agdelte-stepper__indicator"
      ( "display" ∶ "flex"
      ∷ "flex-direction" ∶ "column"
      ∷ "align-items" ∶ "center"
      ∷ [])
  ∷ rule ".agdelte-stepper__number"
      ( "display" ∶ "flex"
      ∷ "align-items" ∶ "center"
      ∷ "justify-content" ∶ "center"
      ∷ "width" ∶ "32px"
      ∷ "height" ∶ "32px"
      ∷ "border-radius" ∶ "50%"
      ∷ "background" ∶ "var(--agdelte-bg-active)"
      ∷ "color" ∶ "var(--agdelte-text-muted)"
      ∷ "font-weight" ∶ "600"
      ∷ "font-size" ∶ "0.875rem"
      ∷ transitionAll
      ∷ [])
  ∷ rule ".agdelte-stepper__step--active .agdelte-stepper__number"
      ( "background" ∶ "var(--agdelte-primary)"
      ∷ "color" ∶ "var(--agdelte-text-light)"
      ∷ [])
  ∷ rule ".agdelte-stepper__step--completed .agdelte-stepper__number"
      ( "background" ∶ "var(--agdelte-success)"
      ∷ "color" ∶ "var(--agdelte-text-light)"
      ∷ [])
  ∷ rule ".agdelte-stepper__step--completed .agdelte-stepper__number::after"
      ( "content" ∶ "\"\\2713\""
      ∷ [])
  ∷ rule ".agdelte-stepper__content"
      ( "display" ∶ "flex"
      ∷ "flex-direction" ∶ "column"
      ∷ "margin-left" ∶ "var(--agdelte-spacing-sm)"
      ∷ "padding-top" ∶ "var(--agdelte-spacing-xs)"
      ∷ [])
  ∷ rule ".agdelte-stepper__label"
      ( "font-weight" ∶ "500"
      ∷ "color" ∶ "var(--agdelte-text)"
      ∷ [])
  ∷ rule ".agdelte-stepper__step--active .agdelte-stepper__label"
      ( "color" ∶ "var(--agdelte-primary)"
      ∷ [])
  ∷ rule ".agdelte-stepper__description"
      ( "font-size" ∶ "0.875rem"
      ∷ "color" ∶ "var(--agdelte-text-muted)"
      ∷ "margin-top" ∶ "var(--agdelte-spacing-xs)"
      ∷ [])
  ∷ rule ".agdelte-stepper__line"
      ( "flex" ∶ "1"
      ∷ "height" ∶ "2px"
      ∷ "background" ∶ "var(--agdelte-border)"
      ∷ "margin" ∶ "16px var(--agdelte-spacing-sm) 0"
      ∷ [])
  ∷ rule ".agdelte-stepper__step--completed .agdelte-stepper__line"
      ( "background" ∶ "var(--agdelte-success)"
      ∷ [])
  ∷ rule ".agdelte-stepper--vertical .agdelte-stepper__line"
      ( "width" ∶ "2px"
      ∷ "height" ∶ "24px"
      ∷ "margin" ∶ "var(--agdelte-spacing-xs) 0 0 16px"
      ∷ "flex" ∶ "none"
      ∷ [])
  -- Clickable stepper
  ∷ rule ".agdelte-stepper--clickable .agdelte-stepper__step"
      ( cursorPointer
      ∷ "background" ∶ "none"
      ∷ "border" ∶ "none"
      ∷ "padding" ∶ "var(--agdelte-spacing-xs)"
      ∷ borderRadius
      ∷ transitionBg
      ∷ [])
  ∷ rule ".agdelte-stepper--clickable .agdelte-stepper__step:hover"
      ( "background" ∶ "var(--agdelte-bg-hover)"
      ∷ [])
  ∷ rule ".agdelte-stepper--clickable .agdelte-stepper__step:focus-visible"
      focusOutline
  -- Clickable step cursor
  ∷ rule ".agdelte-stepper--clickable .agdelte-stepper__step"
      ( cursorPointer
      ∷ [])
  -- Active step number
  ∷ rule ".agdelte-stepper__step--active .agdelte-stepper__number"
      ( "background" ∶ "var(--agdelte-primary)"
      ∷ "color" ∶ "var(--agdelte-text-light)"
      ∷ [])
  -- Completed step number
  ∷ rule ".agdelte-stepper__step--completed .agdelte-stepper__number"
      ( "background" ∶ "var(--agdelte-success, #22c55e)"
      ∷ "color" ∶ "var(--agdelte-text-light)"
      ∷ [])
  ∷ []
