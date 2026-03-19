{-# OPTIONS --without-K #-}

-- CSS styles for the Tooltip control
-- (HTML structure is in Agdelte.Html.Controls)

module Agdelte.Css.Controls.Tooltip where

open import Data.List using (List; []; _∷_)

open import Agdelte.Css.Decl using (Style; _∶_; borderRadius)
open import Agdelte.Css.Stylesheet using (Rule; rule; Stylesheet)

------------------------------------------------------------------------
-- Tooltip rules
------------------------------------------------------------------------

tooltipRules : Stylesheet
tooltipRules =
    rule ".agdelte-tooltip"
      ( "position" ∶ "relative"
      ∷ "display" ∶ "inline-block"
      ∷ [])
  ∷ rule ".agdelte-tooltip__trigger"
      ( "cursor" ∶ "help"
      ∷ [])
  ∷ rule ".agdelte-tooltip__content"
      ( "position" ∶ "absolute"
      ∷ "z-index" ∶ "var(--agdelte-z-tooltip)"
      ∷ "padding" ∶ "var(--agdelte-spacing-xs) var(--agdelte-spacing-sm)"
      ∷ "background" ∶ "var(--agdelte-tooltip-bg)"
      ∷ "color" ∶ "var(--agdelte-tooltip-text)"
      ∷ borderRadius
      ∷ "font-size" ∶ "0.875rem"
      ∷ "white-space" ∶ "nowrap"
      ∷ "opacity" ∶ "0"
      ∷ "visibility" ∶ "hidden"
      ∷ "transition" ∶ "opacity var(--agdelte-transition), visibility var(--agdelte-transition)"
      ∷ "transition-delay" ∶ "0.1s"
      ∷ "pointer-events" ∶ "none"
      ∷ [])
  ∷ rule ".agdelte-tooltip:hover .agdelte-tooltip__content"
      ( "opacity" ∶ "1"
      ∷ "visibility" ∶ "visible"
      ∷ "transition-delay" ∶ "0.3s"
      ∷ [])
  -- Positions
  ∷ rule ".agdelte-tooltip--top .agdelte-tooltip__content"
      ( "bottom" ∶ "100%"
      ∷ "left" ∶ "50%"
      ∷ "transform" ∶ "translateX(-50%)"
      ∷ "margin-bottom" ∶ "var(--agdelte-spacing-xs)"
      ∷ [])
  ∷ rule ".agdelte-tooltip--bottom .agdelte-tooltip__content"
      ( "top" ∶ "100%"
      ∷ "left" ∶ "50%"
      ∷ "transform" ∶ "translateX(-50%)"
      ∷ "margin-top" ∶ "var(--agdelte-spacing-xs)"
      ∷ [])
  ∷ rule ".agdelte-tooltip--left .agdelte-tooltip__content"
      ( "right" ∶ "100%"
      ∷ "top" ∶ "50%"
      ∷ "transform" ∶ "translateY(-50%)"
      ∷ "margin-right" ∶ "var(--agdelte-spacing-xs)"
      ∷ [])
  ∷ rule ".agdelte-tooltip--right .agdelte-tooltip__content"
      ( "left" ∶ "100%"
      ∷ "top" ∶ "50%"
      ∷ "transform" ∶ "translateY(-50%)"
      ∷ "margin-left" ∶ "var(--agdelte-spacing-xs)"
      ∷ [])
  ∷ []
