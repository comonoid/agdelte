{-# OPTIONS --without-K #-}

-- CSS styles for the Breadcrumb control
-- (HTML structure is in Agdelte.Html.Controls)

module Agdelte.Css.Controls.Breadcrumb where

open import Data.List using (List; []; _∷_)

open import Agdelte.Css.Decl using (Style; _∶_; borderRadius; focusOutline; transitionAll; cursorPointer)
open import Agdelte.Css.Stylesheet using (Rule; rule; Stylesheet)

------------------------------------------------------------------------
-- Breadcrumb rules
------------------------------------------------------------------------

breadcrumbRules : Stylesheet
breadcrumbRules =
    rule ".agdelte-breadcrumb"
      ( "padding" ∶ "var(--agdelte-spacing-sm) 0"
      ∷ [])
  ∷ rule ".agdelte-breadcrumb__list"
      ( "display" ∶ "flex"
      ∷ "flex-wrap" ∶ "nowrap"
      ∷ "align-items" ∶ "center"
      ∷ "list-style" ∶ "none"
      ∷ "margin" ∶ "0"
      ∷ "padding" ∶ "0"
      ∷ "gap" ∶ "var(--agdelte-spacing-xs)"
      ∷ "overflow" ∶ "hidden"
      ∷ "text-overflow" ∶ "ellipsis"
      ∷ "white-space" ∶ "nowrap"
      ∷ [])
  ∷ rule ".agdelte-breadcrumb__item"
      ( "display" ∶ "flex"
      ∷ "align-items" ∶ "center"
      ∷ [])
  ∷ rule ".agdelte-breadcrumb__link"
      ( "background" ∶ "transparent"
      ∷ "border" ∶ "none"
      ∷ "padding" ∶ "var(--agdelte-spacing-xs) var(--agdelte-spacing-sm)"
      ∷ "color" ∶ "var(--agdelte-primary)"
      ∷ cursorPointer
      ∷ "font-size" ∶ "inherit"
      ∷ borderRadius
      ∷ transitionAll
      ∷ [])
  ∷ rule ".agdelte-breadcrumb__link:hover"
      ( "background" ∶ "var(--agdelte-bg-hover)"
      ∷ "text-decoration" ∶ "underline"
      ∷ [])
  ∷ rule ".agdelte-breadcrumb__link:focus-visible"
      focusOutline
  ∷ rule ".agdelte-breadcrumb__separator"
      ( "color" ∶ "var(--agdelte-text-muted)"
      ∷ "margin" ∶ "0 var(--agdelte-spacing-xs)"
      ∷ [])
  ∷ rule ".agdelte-breadcrumb__current"
      ( "color" ∶ "var(--agdelte-text)"
      ∷ "font-weight" ∶ "500"
      ∷ "padding" ∶ "var(--agdelte-spacing-xs) var(--agdelte-spacing-sm)"
      ∷ [])
  ∷ []
