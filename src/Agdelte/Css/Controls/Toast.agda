{-# OPTIONS --without-K #-}

-- CSS styles for the Toast control
-- (HTML structure is in Agdelte.Html.Controls)

module Agdelte.Css.Controls.Toast where

open import Data.List using (List; []; _∷_)

open import Agdelte.Css.Decl using (Style; _∶_)
open import Agdelte.Css.Stylesheet using (Rule; rule; Stylesheet)

------------------------------------------------------------------------
-- Toast rules
------------------------------------------------------------------------

toastRules : Stylesheet
toastRules =
    rule ".agdelte-toast-container"
      ( "position" ∶ "fixed"
      ∷ "top" ∶ "var(--agdelte-spacing-md)"
      ∷ "right" ∶ "var(--agdelte-spacing-md)"
      ∷ "display" ∶ "flex"
      ∷ "flex-direction" ∶ "column"
      ∷ "gap" ∶ "var(--agdelte-spacing-sm)"
      ∷ "z-index" ∶ "var(--agdelte-z-toast)"
      ∷ "pointer-events" ∶ "none"
      ∷ [])
  ∷ rule ".agdelte-toast"
      ( "display" ∶ "flex"
      ∷ "align-items" ∶ "center"
      ∷ "gap" ∶ "var(--agdelte-spacing-sm)"
      ∷ "padding" ∶ "var(--agdelte-spacing-sm) var(--agdelte-spacing-md)"
      ∷ "border-radius" ∶ "var(--agdelte-border-radius)"
      ∷ "box-shadow" ∶ "var(--agdelte-shadow)"
      ∷ "color" ∶ "var(--agdelte-text-light)"
      ∷ "pointer-events" ∶ "auto"
      ∷ "animation" ∶ "agdelte-slide-in-right var(--agdelte-transition)"
      ∷ [])
  ∷ rule ".agdelte-toast--info"
      ( "background" ∶ "var(--agdelte-info)"
      ∷ [])
  ∷ rule ".agdelte-toast--success"
      ( "background" ∶ "var(--agdelte-success)"
      ∷ [])
  ∷ rule ".agdelte-toast--warning"
      ( "background" ∶ "var(--agdelte-warning)"
      ∷ "color" ∶ "var(--agdelte-warning-text)"
      ∷ [])
  ∷ rule ".agdelte-toast--error"
      ( "background" ∶ "var(--agdelte-error)"
      ∷ [])
  ∷ rule ".agdelte-toast__message"
      ( "flex" ∶ "1"
      ∷ [])
  ∷ rule ".agdelte-toast__close"
      ( "background" ∶ "transparent"
      ∷ "border" ∶ "none"
      ∷ "color" ∶ "inherit"
      ∷ "cursor" ∶ "pointer"
      ∷ "font-size" ∶ "1.25rem"
      ∷ "line-height" ∶ "1"
      ∷ "opacity" ∶ "0.7"
      ∷ "padding" ∶ "0 var(--agdelte-spacing-xs)"
      ∷ "transition" ∶ "opacity var(--agdelte-transition)"
      ∷ [])
  ∷ rule ".agdelte-toast__close:hover"
      ( "opacity" ∶ "1"
      ∷ [])
  ∷ []
