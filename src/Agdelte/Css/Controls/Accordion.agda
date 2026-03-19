{-# OPTIONS --without-K #-}

-- CSS styles for the Accordion control
-- (HTML structure is in Agdelte.Html.Controls.Accordion)

module Agdelte.Css.Controls.Accordion where

open import Data.List using (List; []; _∷_)

open import Agdelte.Css.Decl using (Style; _∶_; borderRadius; focusOutline; transitionBg; cursorPointer)
open import Agdelte.Css.Stylesheet using (Rule; rule; Stylesheet)

------------------------------------------------------------------------
-- Accordion rules
------------------------------------------------------------------------

accordionRules : Stylesheet
accordionRules =
    rule ".agdelte-accordion"
      ( "display" ∶ "flex"
      ∷ "flex-direction" ∶ "column"
      ∷ "border" ∶ "1px solid var(--agdelte-border)"
      ∷ borderRadius
      ∷ "overflow" ∶ "hidden"
      ∷ [])
  ∷ rule ".agdelte-accordion__item"
      ( "border-bottom" ∶ "1px solid var(--agdelte-border)"
      ∷ [])
  ∷ rule ".agdelte-accordion__item:last-child"
      ( "border-bottom" ∶ "none"
      ∷ [])
  ∷ rule ".agdelte-accordion__header"
      ( "display" ∶ "flex"
      ∷ "align-items" ∶ "center"
      ∷ "justify-content" ∶ "space-between"
      ∷ "width" ∶ "100%"
      ∷ "padding" ∶ "var(--agdelte-spacing-md)"
      ∷ "background" ∶ "var(--agdelte-bg)"
      ∷ "border" ∶ "none"
      ∷ cursorPointer
      ∷ "font-size" ∶ "inherit"
      ∷ "color" ∶ "var(--agdelte-text)"
      ∷ "text-align" ∶ "left"
      ∷ transitionBg
      ∷ [])
  ∷ rule ".agdelte-accordion__header:hover"
      ( "background" ∶ "var(--agdelte-bg-hover)"
      ∷ [])
  ∷ rule ".agdelte-accordion__header:focus-visible"
      focusOutline
  ∷ rule ".agdelte-accordion__title"
      ( "font-weight" ∶ "500"
      ∷ [])
  ∷ rule ".agdelte-accordion__icon"
      ( "font-size" ∶ "0.75rem"
      ∷ "color" ∶ "var(--agdelte-text-muted)"
      ∷ "transition" ∶ "transform var(--agdelte-transition)"
      ∷ [])
  ∷ rule ".agdelte-accordion__icon--open"
      ( "transform" ∶ "rotate(180deg)"
      ∷ [])
  ∷ rule ".agdelte-accordion__content"
      ( "padding" ∶ "var(--agdelte-spacing-md)"
      ∷ "background" ∶ "var(--agdelte-bg)"
      ∷ "border-top" ∶ "1px solid var(--agdelte-border)"
      ∷ "animation" ∶ "agdelte-slide-down var(--agdelte-transition)"
      ∷ [])
  -- Multi-open variant (extension point)
  ∷ rule ".agdelte-accordion--multi" []
  ∷ []
