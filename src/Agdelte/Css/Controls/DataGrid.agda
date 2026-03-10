{-# OPTIONS --without-K #-}

-- CSS styles for the DataGrid control
-- (HTML structure is in Agdelte.Html.Controls.DataGrid)

module Agdelte.Css.Controls.DataGrid where

open import Data.List using (List; []; _∷_)

open import Agdelte.Css.Decl using (Style; _∶_)
open import Agdelte.Css.Stylesheet using (Rule; rule; Stylesheet)

------------------------------------------------------------------------
-- DataGrid rules
------------------------------------------------------------------------

dataGridRules : Stylesheet
dataGridRules =
  -- Grid (flex-based)
    rule ".agdelte-grid"
      ( "display" ∶ "flex"
      ∷ "flex-direction" ∶ "column"
      ∷ "border" ∶ "1px solid var(--agdelte-border)"
      ∷ "border-radius" ∶ "var(--agdelte-border-radius)"
      ∷ "overflow" ∶ "hidden"
      ∷ [])
  ∷ rule ".agdelte-grid__header"
      ( "display" ∶ "flex"
      ∷ "background" ∶ "var(--agdelte-bg-hover)"
      ∷ "border-bottom" ∶ "1px solid var(--agdelte-border)"
      ∷ "font-weight" ∶ "600"
      ∷ [])
  ∷ rule ".agdelte-grid__body"
      ( "display" ∶ "flex"
      ∷ "flex-direction" ∶ "column"
      ∷ [])
  ∷ rule ".agdelte-grid__row"
      ( "display" ∶ "flex"
      ∷ "border-bottom" ∶ "1px solid var(--agdelte-border)"
      ∷ "transition" ∶ "background var(--agdelte-transition)"
      ∷ [])
  ∷ rule ".agdelte-grid__row:last-child"
      ( "border-bottom" ∶ "none"
      ∷ [])
  ∷ rule ".agdelte-grid__row:hover"
      ( "background" ∶ "var(--agdelte-bg-hover)"
      ∷ [])
  ∷ rule ".agdelte-grid__row--clickable"
      ( "cursor" ∶ "pointer"
      ∷ [])
  ∷ rule ".agdelte-grid__row--clickable:hover"
      ( "background" ∶ "var(--agdelte-bg-active)"
      ∷ [])
  ∷ rule ".agdelte-grid__cell"
      ( "padding" ∶ "var(--agdelte-spacing-sm) var(--agdelte-spacing-md)"
      ∷ "overflow" ∶ "hidden"
      ∷ "text-overflow" ∶ "ellipsis"
      ∷ "white-space" ∶ "nowrap"
      ∷ [])
  ∷ rule ".agdelte-grid__cell--header"
      ( "font-weight" ∶ "600"
      ∷ "color" ∶ "var(--agdelte-text)"
      ∷ [])
  ∷ rule ".agdelte-grid__action"
      ( "padding" ∶ "var(--agdelte-spacing-xs) var(--agdelte-spacing-sm)"
      ∷ "background" ∶ "var(--agdelte-primary)"
      ∷ "color" ∶ "var(--agdelte-text-light)"
      ∷ "border" ∶ "none"
      ∷ "border-radius" ∶ "var(--agdelte-border-radius)"
      ∷ "cursor" ∶ "pointer"
      ∷ "font-size" ∶ "0.875rem"
      ∷ [])
  ∷ rule ".agdelte-grid__action:hover"
      ( "background" ∶ "var(--agdelte-primary-hover)"
      ∷ [])
  -- Simple table
  ∷ rule ".agdelte-table"
      ( "width" ∶ "100%"
      ∷ "border-collapse" ∶ "collapse"
      ∷ "border" ∶ "1px solid var(--agdelte-border)"
      ∷ [])
  ∷ rule ".agdelte-table th, .agdelte-table td"
      ( "padding" ∶ "var(--agdelte-spacing-sm) var(--agdelte-spacing-md)"
      ∷ "border" ∶ "1px solid var(--agdelte-border)"
      ∷ "text-align" ∶ "left"
      ∷ [])
  ∷ rule ".agdelte-table th"
      ( "background" ∶ "var(--agdelte-bg-hover)"
      ∷ "font-weight" ∶ "600"
      ∷ [])
  ∷ rule ".agdelte-table tr:hover"
      ( "background" ∶ "var(--agdelte-bg-hover)"
      ∷ [])
  ∷ []
