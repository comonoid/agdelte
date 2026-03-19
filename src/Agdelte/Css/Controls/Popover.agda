{-# OPTIONS --without-K #-}

-- CSS styles for the Popover control
-- (HTML structure is in Agdelte.Html.Controls.Popover)

module Agdelte.Css.Controls.Popover where

open import Data.List using (List; []; _∷_)

open import Agdelte.Css.Decl using (Style; _∶_; borderRadius; focusOutline; transitionAll; transitionBg; cursorPointer)
open import Agdelte.Css.Stylesheet using (Rule; rule; Stylesheet)

------------------------------------------------------------------------
-- Popover rules
------------------------------------------------------------------------

popoverRules : Stylesheet
popoverRules =
    rule ".agdelte-popover-container"
      ( "position" ∶ "relative"
      ∷ "display" ∶ "inline-block"
      ∷ [])
  ∷ rule ".agdelte-popover__trigger"
      ( "background" ∶ "transparent"
      ∷ "border" ∶ "none"
      ∷ cursorPointer
      ∷ "padding" ∶ "0"
      ∷ "font" ∶ "inherit"
      ∷ "color" ∶ "inherit"
      ∷ [])
  ∷ rule ".agdelte-popover"
      ( "position" ∶ "absolute"
      ∷ "z-index" ∶ "var(--agdelte-z-popover)"
      ∷ "padding" ∶ "var(--agdelte-spacing-md)"
      ∷ "background" ∶ "var(--agdelte-bg)"
      ∷ "border" ∶ "1px solid var(--agdelte-border)"
      ∷ borderRadius
      ∷ "box-shadow" ∶ "var(--agdelte-shadow-lg)"
      ∷ "animation" ∶ "agdelte-scale-in var(--agdelte-transition)"
      ∷ "min-width" ∶ "200px"
      ∷ [])
  -- Position variants
  ∷ rule ".agdelte-popover--bottom"
      ( "top" ∶ "100%"
      ∷ "left" ∶ "0"
      ∷ "margin-top" ∶ "var(--agdelte-spacing-xs)"
      ∷ [])
  ∷ rule ".agdelte-popover--top"
      ( "bottom" ∶ "100%"
      ∷ "left" ∶ "0"
      ∷ "margin-bottom" ∶ "var(--agdelte-spacing-xs)"
      ∷ [])
  ∷ rule ".agdelte-popover--left"
      ( "right" ∶ "100%"
      ∷ "top" ∶ "0"
      ∷ "margin-right" ∶ "var(--agdelte-spacing-xs)"
      ∷ [])
  ∷ rule ".agdelte-popover--right"
      ( "left" ∶ "100%"
      ∷ "top" ∶ "0"
      ∷ "margin-left" ∶ "var(--agdelte-spacing-xs)"
      ∷ [])
  -- Content wrapper (empty rule — extension point)
  ∷ rule ".agdelte-popover__content" []
  -- Header
  ∷ rule ".agdelte-popover__header"
      ( "display" ∶ "flex"
      ∷ "align-items" ∶ "center"
      ∷ "justify-content" ∶ "space-between"
      ∷ "margin-bottom" ∶ "var(--agdelte-spacing-sm)"
      ∷ "padding-bottom" ∶ "var(--agdelte-spacing-sm)"
      ∷ "border-bottom" ∶ "1px solid var(--agdelte-border)"
      ∷ [])
  ∷ rule ".agdelte-popover__title"
      ( "font-weight" ∶ "600"
      ∷ "color" ∶ "var(--agdelte-text)"
      ∷ [])
  ∷ rule ".agdelte-popover__close"
      ( "width" ∶ "24px"
      ∷ "height" ∶ "24px"
      ∷ "padding" ∶ "0"
      ∷ "background" ∶ "transparent"
      ∷ "border" ∶ "none"
      ∷ cursorPointer
      ∷ "font-size" ∶ "1.25rem"
      ∷ "color" ∶ "var(--agdelte-text-muted)"
      ∷ "line-height" ∶ "1"
      ∷ [])
  ∷ rule ".agdelte-popover__close:hover"
      ( "color" ∶ "var(--agdelte-text)"
      ∷ [])
  ∷ rule ".agdelte-popover__close:focus-visible"
      focusOutline
  -- Menu variant
  ∷ rule ".agdelte-popover--menu"
      ( "padding" ∶ "var(--agdelte-spacing-xs)"
      ∷ [])
  ∷ rule ".agdelte-popover__menu-item"
      ( "display" ∶ "block"
      ∷ "width" ∶ "100%"
      ∷ "padding" ∶ "var(--agdelte-spacing-sm) var(--agdelte-spacing-md)"
      ∷ "background" ∶ "transparent"
      ∷ "border" ∶ "none"
      ∷ borderRadius
      ∷ cursorPointer
      ∷ "color" ∶ "var(--agdelte-text)"
      ∷ "text-align" ∶ "left"
      ∷ "font-size" ∶ "inherit"
      ∷ transitionBg
      ∷ [])
  ∷ rule ".agdelte-popover__menu-item:hover"
      ( "background" ∶ "var(--agdelte-bg-hover)"
      ∷ [])
  ∷ rule ".agdelte-popover__menu-item:focus-visible"
      focusOutline
  -- Confirm variant
  ∷ rule ".agdelte-popover--confirm"
      ( "min-width" ∶ "240px"
      ∷ [])
  ∷ rule ".agdelte-popover__message"
      ( "margin-bottom" ∶ "var(--agdelte-spacing-md)"
      ∷ "color" ∶ "var(--agdelte-text)"
      ∷ [])
  ∷ rule ".agdelte-popover__actions"
      ( "display" ∶ "flex"
      ∷ "justify-content" ∶ "flex-end"
      ∷ "gap" ∶ "var(--agdelte-spacing-sm)"
      ∷ [])
  ∷ rule ".agdelte-popover__btn"
      ( "padding" ∶ "var(--agdelte-spacing-sm) var(--agdelte-spacing-md)"
      ∷ "border" ∶ "1px solid var(--agdelte-border)"
      ∷ borderRadius
      ∷ cursorPointer
      ∷ "font-size" ∶ "inherit"
      ∷ transitionAll
      ∷ [])
  ∷ rule ".agdelte-popover__btn--cancel"
      ( "background" ∶ "var(--agdelte-bg)"
      ∷ "color" ∶ "var(--agdelte-text)"
      ∷ [])
  ∷ rule ".agdelte-popover__btn--cancel:hover"
      ( "background" ∶ "var(--agdelte-bg-hover)"
      ∷ [])
  ∷ rule ".agdelte-popover__btn--confirm"
      ( "background" ∶ "var(--agdelte-primary)"
      ∷ "border-color" ∶ "var(--agdelte-primary)"
      ∷ "color" ∶ "var(--agdelte-text-light)"
      ∷ [])
  ∷ rule ".agdelte-popover__btn--confirm:hover"
      ( "background" ∶ "var(--agdelte-primary-hover)"
      ∷ "border-color" ∶ "var(--agdelte-primary-hover)"
      ∷ [])
  -- Help/Info icons
  ∷ rule ".agdelte-help-icon, .agdelte-info-icon"
      ( "display" ∶ "inline-flex"
      ∷ "align-items" ∶ "center"
      ∷ "justify-content" ∶ "center"
      ∷ "width" ∶ "16px"
      ∷ "height" ∶ "16px"
      ∷ "border-radius" ∶ "50%"
      ∷ "background" ∶ "var(--agdelte-text-muted)"
      ∷ "color" ∶ "var(--agdelte-text-light)"
      ∷ "font-size" ∶ "0.625rem"
      ∷ "font-weight" ∶ "bold"
      ∷ "cursor" ∶ "help"
      ∷ [])
  ∷ []
