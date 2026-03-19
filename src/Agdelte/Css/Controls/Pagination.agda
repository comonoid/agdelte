{-# OPTIONS --without-K #-}

-- CSS styles for the Pagination control
-- (HTML structure is in Agdelte.Html.Controls.Pagination)

module Agdelte.Css.Controls.Pagination where

open import Data.List using (List; []; _∷_)

open import Agdelte.Css.Decl using (Style; _∶_; borderRadius; focusOutline; transitionAll; cursorPointer)
open import Agdelte.Css.Stylesheet using (Rule; rule; Stylesheet)

------------------------------------------------------------------------
-- Pagination rules
------------------------------------------------------------------------

paginationRules : Stylesheet
paginationRules =
    rule ".agdelte-pagination"
      ( "display" ∶ "flex"
      ∷ "align-items" ∶ "center"
      ∷ "gap" ∶ "var(--agdelte-spacing-sm)"
      ∷ [])
  ∷ rule ".agdelte-pagination--compact"
      ( "gap" ∶ "var(--agdelte-spacing-xs)"
      ∷ [])
  ∷ rule ".agdelte-pagination__btn"
      ( "padding" ∶ "var(--agdelte-spacing-xs) var(--agdelte-spacing-sm)"
      ∷ "background" ∶ "var(--agdelte-bg)"
      ∷ "border" ∶ "1px solid var(--agdelte-border)"
      ∷ borderRadius
      ∷ cursorPointer
      ∷ "color" ∶ "var(--agdelte-text)"
      ∷ transitionAll
      ∷ [])
  ∷ rule ".agdelte-pagination__btn:hover:not(:disabled)"
      ( "background" ∶ "var(--agdelte-bg-hover)"
      ∷ "border-color" ∶ "var(--agdelte-primary)"
      ∷ [])
  ∷ rule ".agdelte-pagination__btn:focus-visible"
      focusOutline
  ∷ rule ".agdelte-pagination__btn:disabled"
      ( "opacity" ∶ "0.5"
      ∷ "cursor" ∶ "not-allowed"
      ∷ [])
  ∷ rule ".agdelte-pagination__page"
      ( "min-width" ∶ "32px"
      ∷ "height" ∶ "32px"
      ∷ "padding" ∶ "var(--agdelte-spacing-xs)"
      ∷ "background" ∶ "var(--agdelte-bg)"
      ∷ "border" ∶ "1px solid var(--agdelte-border)"
      ∷ borderRadius
      ∷ cursorPointer
      ∷ "color" ∶ "var(--agdelte-text)"
      ∷ transitionAll
      ∷ [])
  ∷ rule ".agdelte-pagination__page:hover"
      ( "background" ∶ "var(--agdelte-bg-hover)"
      ∷ "border-color" ∶ "var(--agdelte-primary)"
      ∷ [])
  ∷ rule ".agdelte-pagination__page:focus-visible"
      focusOutline
  ∷ rule ".agdelte-pagination__page--active"
      ( "background" ∶ "var(--agdelte-primary)"
      ∷ "border-color" ∶ "var(--agdelte-primary)"
      ∷ "color" ∶ "var(--agdelte-text-light)"
      ∷ [])
  ∷ rule ".agdelte-pagination__info, .agdelte-pagination__current"
      ( "color" ∶ "var(--agdelte-text)"
      ∷ "padding" ∶ "0 var(--agdelte-spacing-sm)"
      ∷ [])
  ∷ rule ".agdelte-pagination__ellipsis"
      ( "color" ∶ "var(--agdelte-text-muted)"
      ∷ "padding" ∶ "0 var(--agdelte-spacing-xs)"
      ∷ [])
  ∷ []
