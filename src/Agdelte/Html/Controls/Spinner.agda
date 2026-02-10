{-# OPTIONS --without-K #-}

-- Spinner: Loading spinners
-- CSS-animated loading indicators
-- CSS classes: .agdelte-spinner, .agdelte-spinner--small,
--              .agdelte-spinner--large, .agdelte-spinner--inline,
--              .agdelte-spinner-overlay, .agdelte-dot-spinner,
--              .agdelte-pulse-spinner, .agdelte-bar-spinner

module Agdelte.Html.Controls.Spinner where

open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false; if_then_else_)

open import Agdelte.Reactive.Node

------------------------------------------------------------------------
-- Basic spinner
------------------------------------------------------------------------

-- | Simple spinning circle (CSS handles animation)
spinner : ∀ {M A} → Node M A
spinner = div (class "agdelte-spinner" ∷ []) []

-- | Spinner with custom size
spinnerSized : ∀ {M A} → String → Node M A
spinnerSized size =
  div ( class "agdelte-spinner"
      ∷ style "width" size
      ∷ style "height" size
      ∷ [] ) []

-- | Small spinner
spinnerSmall : ∀ {M A} → Node M A
spinnerSmall = div (class "agdelte-spinner agdelte-spinner--small" ∷ []) []

-- | Large spinner
spinnerLarge : ∀ {M A} → Node M A
spinnerLarge = div (class "agdelte-spinner agdelte-spinner--large" ∷ []) []

------------------------------------------------------------------------
-- Spinner with text
------------------------------------------------------------------------

-- | Spinner with label text below
spinnerWithText : ∀ {M A} → String → Node M A
spinnerWithText label' =
  div (class "agdelte-spinner-container" ∷ [])
    ( div (class "agdelte-spinner" ∷ []) []
    ∷ span (class "agdelte-spinner__text" ∷ []) (text label' ∷ [])
    ∷ [] )

------------------------------------------------------------------------
-- Dot spinner (three bouncing dots)
------------------------------------------------------------------------

-- | Three bouncing dots animation
dotSpinner : ∀ {M A} → Node M A
dotSpinner =
  div (class "agdelte-dot-spinner" ∷ [])
    ( span (class "agdelte-dot-spinner__dot" ∷ []) []
    ∷ span (class "agdelte-dot-spinner__dot" ∷ []) []
    ∷ span (class "agdelte-dot-spinner__dot" ∷ []) []
    ∷ [] )

------------------------------------------------------------------------
-- Pulse spinner (growing/shrinking circle)
------------------------------------------------------------------------

-- | Pulsing circle animation
pulseSpinner : ∀ {M A} → Node M A
pulseSpinner = div (class "agdelte-pulse-spinner" ∷ []) []

------------------------------------------------------------------------
-- Bar spinner (horizontal loading bar)
------------------------------------------------------------------------

-- | Horizontal indeterminate loading bar
barSpinner : ∀ {M A} → Node M A
barSpinner =
  div (class "agdelte-bar-spinner" ∷ [])
    ( div (class "agdelte-bar-spinner__bar" ∷ []) []
    ∷ [] )

------------------------------------------------------------------------
-- Overlay spinner (full-screen with backdrop)
------------------------------------------------------------------------

-- | Full-screen overlay with centered spinner
overlaySpinner : ∀ {M A} → Node M A
overlaySpinner =
  div (class "agdelte-spinner-overlay" ∷ [])
    ( div (class "agdelte-spinner agdelte-spinner--large" ∷ []) []
    ∷ [] )

-- | Full-screen overlay with spinner and text
overlaySpinnerWithText : ∀ {M A} → String → Node M A
overlaySpinnerWithText label' =
  div (class "agdelte-spinner-overlay" ∷ [])
    ( div (class "agdelte-spinner-container" ∷ [])
        ( div (class "agdelte-spinner agdelte-spinner--large" ∷ []) []
        ∷ span (class "agdelte-spinner__text" ∷ []) (text label' ∷ [])
        ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- Inline spinner (for buttons, inputs)
------------------------------------------------------------------------

-- | Small inline spinner for use in buttons
inlineSpinner : ∀ {M A} → Node M A
inlineSpinner = span (class "agdelte-spinner agdelte-spinner--inline" ∷ []) []

------------------------------------------------------------------------
-- Conditional spinner
------------------------------------------------------------------------

-- | Show spinner while loading, content when done
withSpinner : ∀ {M A}
            → (M → Bool)       -- isLoading
            → Node M A         -- content when loaded
            → Node M A
withSpinner {M} isLoading content =
  div (class "agdelte-spinner-wrapper" ∷ [])
    ( when isLoading spinner
    ∷ when (not' isLoading) content
    ∷ [] )
  where
    not' : (M → Bool) → M → Bool
    not' f m = if f m then false else true
