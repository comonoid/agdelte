{-# OPTIONS --without-K #-}

-- CSS styles for the Modal control
-- (HTML structure is in Agdelte.Html.Controls)

module Agdelte.Css.Controls.Modal where

open import Data.List using (List; []; _∷_)

open import Agdelte.Css.Decl using (Style; _∶_)
open import Agdelte.Css.Stylesheet using (Rule; rule; Stylesheet)

------------------------------------------------------------------------
-- Modal rules
------------------------------------------------------------------------

modalRules : Stylesheet
modalRules =
    rule ".agdelte-modal"
      ( "position" ∶ "fixed"
      ∷ "top" ∶ "0"
      ∷ "right" ∶ "0"
      ∷ "bottom" ∶ "0"
      ∷ "left" ∶ "0"
      ∷ "display" ∶ "flex"
      ∷ "align-items" ∶ "center"
      ∷ "justify-content" ∶ "center"
      ∷ "z-index" ∶ "var(--agdelte-z-modal)"
      ∷ [])
  ∷ rule ".agdelte-modal__backdrop"
      ( "position" ∶ "absolute"
      ∷ "top" ∶ "0"
      ∷ "right" ∶ "0"
      ∷ "bottom" ∶ "0"
      ∷ "left" ∶ "0"
      ∷ "background" ∶ "var(--agdelte-backdrop)"
      ∷ "animation" ∶ "agdelte-fade-in var(--agdelte-transition)"
      ∷ [])
  ∷ rule ".agdelte-modal__content"
      ( "position" ∶ "relative"
      ∷ "background" ∶ "var(--agdelte-bg)"
      ∷ "border-radius" ∶ "var(--agdelte-border-radius)"
      ∷ "box-shadow" ∶ "var(--agdelte-shadow-lg)"
      ∷ "max-width" ∶ "90vw"
      ∷ "max-height" ∶ "90vh"
      ∷ "overflow" ∶ "auto"
      ∷ "animation" ∶ "agdelte-scale-in var(--agdelte-transition)"
      ∷ [])
  ∷ rule ".agdelte-modal__dialog"
      ( "padding" ∶ "var(--agdelte-spacing-lg)"
      ∷ "min-width" ∶ "300px"
      ∷ [])
  ∷ rule ".agdelte-modal__title"
      ( "margin" ∶ "0 0 var(--agdelte-spacing-md)"
      ∷ "font-size" ∶ "1.25rem"
      ∷ "color" ∶ "var(--agdelte-text)"
      ∷ [])
  ∷ rule ".agdelte-modal__message"
      ( "margin" ∶ "0 0 var(--agdelte-spacing-lg)"
      ∷ "color" ∶ "var(--agdelte-text-muted)"
      ∷ [])
  ∷ rule ".agdelte-modal__actions"
      ( "display" ∶ "flex"
      ∷ "justify-content" ∶ "flex-end"
      ∷ "gap" ∶ "var(--agdelte-spacing-sm)"
      ∷ [])
  ∷ rule ".agdelte-modal__btn"
      ( "padding" ∶ "var(--agdelte-spacing-sm) var(--agdelte-spacing-md)"
      ∷ "border" ∶ "1px solid var(--agdelte-border)"
      ∷ "border-radius" ∶ "var(--agdelte-border-radius)"
      ∷ "cursor" ∶ "pointer"
      ∷ "font-size" ∶ "inherit"
      ∷ "transition" ∶ "all var(--agdelte-transition)"
      ∷ [])
  ∷ rule ".agdelte-modal__btn--cancel"
      ( "background" ∶ "var(--agdelte-bg)"
      ∷ "color" ∶ "var(--agdelte-text)"
      ∷ [])
  ∷ rule ".agdelte-modal__btn--cancel:hover"
      ( "background" ∶ "var(--agdelte-bg-hover)"
      ∷ [])
  ∷ rule ".agdelte-modal__btn--confirm, .agdelte-modal__btn--ok"
      ( "background" ∶ "var(--agdelte-primary)"
      ∷ "border-color" ∶ "var(--agdelte-primary)"
      ∷ "color" ∶ "var(--agdelte-text-light)"
      ∷ [])
  ∷ rule ".agdelte-modal__btn--confirm:hover, .agdelte-modal__btn--ok:hover"
      ( "background" ∶ "var(--agdelte-primary-hover)"
      ∷ "border-color" ∶ "var(--agdelte-primary-hover)"
      ∷ [])
  ∷ rule ".agdelte-modal__btn:focus-visible"
      ( "outline" ∶ "2px solid var(--agdelte-primary)"
      ∷ "outline-offset" ∶ "2px"
      ∷ [])
  ∷ []
