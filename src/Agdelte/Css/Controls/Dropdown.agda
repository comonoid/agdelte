{-# OPTIONS --without-K #-}

-- CSS styles for the Dropdown control
-- (HTML structure is in Agdelte.Html.Controls.Dropdown)

module Agdelte.Css.Controls.Dropdown where

open import Data.List using (List; []; _∷_)

open import Agdelte.Css.Decl using (Style; _∶_)
open import Agdelte.Css.Stylesheet using (Rule; rule; Stylesheet)

------------------------------------------------------------------------
-- Dropdown rules
------------------------------------------------------------------------

dropdownRules : Stylesheet
dropdownRules =
    rule ".agdelte-dropdown"
      ( "position" ∶ "relative"
      ∷ "display" ∶ "inline-block"
      ∷ [])
  ∷ rule ".agdelte-dropdown__trigger"
      ( "display" ∶ "flex"
      ∷ "align-items" ∶ "center"
      ∷ "justify-content" ∶ "space-between"
      ∷ "gap" ∶ "var(--agdelte-spacing-sm)"
      ∷ "padding" ∶ "var(--agdelte-spacing-sm) var(--agdelte-spacing-md)"
      ∷ "background" ∶ "var(--agdelte-bg)"
      ∷ "border" ∶ "1px solid var(--agdelte-border)"
      ∷ "border-radius" ∶ "var(--agdelte-border-radius)"
      ∷ "cursor" ∶ "pointer"
      ∷ "font-size" ∶ "inherit"
      ∷ "min-width" ∶ "150px"
      ∷ "transition" ∶ "all var(--agdelte-transition)"
      ∷ [])
  ∷ rule ".agdelte-dropdown__trigger:hover"
      ( "border-color" ∶ "var(--agdelte-primary)"
      ∷ [])
  ∷ rule ".agdelte-dropdown__trigger::after"
      ( "content" ∶ "\"\""
      ∷ "border" ∶ "4px solid transparent"
      ∷ "border-top-color" ∶ "var(--agdelte-text-muted)"
      ∷ "margin-top" ∶ "4px"
      ∷ [])
  ∷ rule ".agdelte-dropdown--open .agdelte-dropdown__trigger::after"
      ( "border-top-color" ∶ "transparent"
      ∷ "border-bottom-color" ∶ "var(--agdelte-text-muted)"
      ∷ "margin-top" ∶ "-4px"
      ∷ [])
  ∷ rule ".agdelte-dropdown__backdrop"
      ( "position" ∶ "fixed"
      ∷ "top" ∶ "0"
      ∷ "right" ∶ "0"
      ∷ "bottom" ∶ "0"
      ∷ "left" ∶ "0"
      ∷ "z-index" ∶ "calc(var(--agdelte-z-dropdown) - 1)"
      ∷ [])
  ∷ rule ".agdelte-dropdown__menu"
      ( "position" ∶ "absolute"
      ∷ "top" ∶ "100%"
      ∷ "left" ∶ "0"
      ∷ "right" ∶ "0"
      ∷ "margin-top" ∶ "var(--agdelte-spacing-xs)"
      ∷ "background" ∶ "var(--agdelte-bg)"
      ∷ "border" ∶ "1px solid var(--agdelte-border)"
      ∷ "border-radius" ∶ "var(--agdelte-border-radius)"
      ∷ "box-shadow" ∶ "var(--agdelte-shadow)"
      ∷ "max-height" ∶ "200px"
      ∷ "overflow" ∶ "auto"
      ∷ "z-index" ∶ "var(--agdelte-z-dropdown)"
      ∷ "animation" ∶ "agdelte-slide-down var(--agdelte-transition)"
      ∷ [])
  ∷ rule ".agdelte-dropdown__option"
      ( "padding" ∶ "var(--agdelte-spacing-sm) var(--agdelte-spacing-md)"
      ∷ "cursor" ∶ "pointer"
      ∷ "color" ∶ "var(--agdelte-text)"
      ∷ "transition" ∶ "background var(--agdelte-transition)"
      ∷ [])
  ∷ rule ".agdelte-dropdown__option:hover"
      ( "background" ∶ "var(--agdelte-bg-hover)"
      ∷ [])
  ∷ rule ".agdelte-dropdown__option:focus-visible"
      ( "background" ∶ "var(--agdelte-bg-hover)"
      ∷ "outline" ∶ "2px solid var(--agdelte-primary)"
      ∷ "outline-offset" ∶ "-2px"
      ∷ [])
  ∷ rule ".agdelte-dropdown__option--selected"
      ( "background" ∶ "var(--agdelte-bg-active)"
      ∷ "color" ∶ "var(--agdelte-primary)"
      ∷ [])
  ∷ rule ".agdelte-dropdown__option--highlighted"
      ( "background" ∶ "var(--agdelte-bg-hover)"
      ∷ "outline" ∶ "2px solid var(--agdelte-primary)"
      ∷ "outline-offset" ∶ "-2px"
      ∷ [])
  ∷ []
