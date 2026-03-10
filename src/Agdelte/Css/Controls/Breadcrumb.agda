{-# OPTIONS --without-K #-}

-- CSS styles for the Breadcrumb control
-- (HTML structure is in Agdelte.Html.Controls)

module Agdelte.Css.Controls.Breadcrumb where

open import Data.List using (List; []; _∷_)

open import Agdelte.Css.Decl using (Style; _∶_)
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
      ∷ "flex-wrap" ∶ "wrap"
      ∷ "align-items" ∶ "center"
      ∷ "list-style" ∶ "none"
      ∷ "margin" ∶ "0"
      ∷ "padding" ∶ "0"
      ∷ "gap" ∶ "var(--agdelte-spacing-xs)"
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
      ∷ "cursor" ∶ "pointer"
      ∷ "font-size" ∶ "inherit"
      ∷ "border-radius" ∶ "var(--agdelte-border-radius)"
      ∷ "transition" ∶ "all var(--agdelte-transition)"
      ∷ [])
  ∷ rule ".agdelte-breadcrumb__link:hover"
      ( "background" ∶ "var(--agdelte-bg-hover)"
      ∷ "text-decoration" ∶ "underline"
      ∷ [])
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
