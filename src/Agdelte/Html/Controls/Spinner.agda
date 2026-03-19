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
open import Data.Bool using (Bool; true; false; if_then_else_; not)
open import Data.Maybe using (Maybe; just; nothing)
open import Function using (_∘_)

open import Agdelte.Reactive.Node

------------------------------------------------------------------------
-- Spinner configuration
------------------------------------------------------------------------

data SpinnerKind : Set where
  circle dot pulse bar : SpinnerKind

data SpinnerSize : Set where
  default' small large : SpinnerSize
  custom : String → SpinnerSize

record SpinnerConfig : Set where
  constructor mkSpinnerConfig
  field
    kind    : SpinnerKind
    size    : SpinnerSize
    text'   : Maybe String
    overlay : Bool
    inline  : Bool

defaultSpinner : SpinnerConfig
defaultSpinner = mkSpinnerConfig circle default' nothing false false

------------------------------------------------------------------------
-- Core spinner rendering
------------------------------------------------------------------------

private
  srOnly : ∀ {M A} → Node M A
  srOnly = span (class "agdelte-spinner__sr" ∷ []) (text "Loading..." ∷ [])

  sizeClass : SpinnerSize → String
  sizeClass default' = ""
  sizeClass small    = " agdelte-spinner--small"
  sizeClass large    = " agdelte-spinner--large"
  sizeClass (custom _) = ""

  sizeAttrs : ∀ {M A} → SpinnerSize → List (Attr M A)
  sizeAttrs (custom s) = style "width" s ∷ style "height" s ∷ []
  sizeAttrs _          = []

  renderCircle : ∀ {M A} → SpinnerSize → Bool → Node M A
  renderCircle sz inl =
    let cls = "agdelte-spinner" ++ sizeClass sz
                ++ (if inl then " agdelte-spinner--inline" else "")
        tag = if inl then span else div
    in tag (class cls ∷ attr "role" "status" ∷ sizeAttrs sz) (srOnly ∷ [])

  renderDot : ∀ {M A} → Node M A
  renderDot =
    div (class "agdelte-dot-spinner" ∷ attr "role" "status" ∷ [])
      ( span (class "agdelte-dot-spinner__dot" ∷ []) []
      ∷ span (class "agdelte-dot-spinner__dot" ∷ []) []
      ∷ span (class "agdelte-dot-spinner__dot" ∷ []) []
      ∷ srOnly ∷ [] )

  renderPulse : ∀ {M A} → Node M A
  renderPulse =
    div (class "agdelte-pulse-spinner" ∷ attr "role" "status" ∷ []) (srOnly ∷ [])

  renderBar : ∀ {M A} → Node M A
  renderBar =
    div (class "agdelte-bar-spinner" ∷ attr "role" "status" ∷ [])
      ( div (class "agdelte-bar-spinner__bar" ∷ []) []
      ∷ srOnly ∷ [] )

  renderKind : ∀ {M A} → SpinnerKind → SpinnerSize → Bool → Node M A
  renderKind circle sz inl = renderCircle sz inl
  renderKind dot    _  _   = renderDot
  renderKind pulse  _  _   = renderPulse
  renderKind bar    _  _   = renderBar

  wrapLabel : ∀ {M A} → Maybe String → Node M A → Node M A
  wrapLabel nothing inner = inner
  wrapLabel (just lbl) inner =
    div (class "agdelte-spinner-container" ∷ attr "role" "status" ∷ [])
      ( inner
      ∷ span (class "agdelte-spinner__text" ∷ []) (text lbl ∷ [])
      ∷ [] )

  wrapOverlay : ∀ {M A} → Bool → Node M A → Node M A
  wrapOverlay false inner = inner
  wrapOverlay true  inner =
    div (class "agdelte-spinner-overlay" ∷ attr "role" "status" ∷ []) (inner ∷ [])

-- | Main spinner function with full configuration
spinnerWith : ∀ {M A} → SpinnerConfig → Node M A
spinnerWith cfg =
  let open SpinnerConfig cfg
  in wrapOverlay overlay (wrapLabel text' (renderKind kind size inline))

------------------------------------------------------------------------
-- Backward-compatible convenience functions
------------------------------------------------------------------------

spinner : ∀ {M A} → Node M A
spinner = spinnerWith defaultSpinner

spinnerSized : ∀ {M A} → String → Node M A
spinnerSized s = spinnerWith (record defaultSpinner { size = custom s })

spinnerSmall : ∀ {M A} → Node M A
spinnerSmall = spinnerWith (record defaultSpinner { size = small })

spinnerLarge : ∀ {M A} → Node M A
spinnerLarge = spinnerWith (record defaultSpinner { size = large })

spinnerWithText : ∀ {M A} → String → Node M A
spinnerWithText lbl = spinnerWith (record defaultSpinner { text' = just lbl })

dotSpinner : ∀ {M A} → Node M A
dotSpinner = spinnerWith (record defaultSpinner { kind = dot })

pulseSpinner : ∀ {M A} → Node M A
pulseSpinner = spinnerWith (record defaultSpinner { kind = pulse })

barSpinner : ∀ {M A} → Node M A
barSpinner = spinnerWith (record defaultSpinner { kind = bar })

overlaySpinner : ∀ {M A} → Node M A
overlaySpinner = spinnerWith (record defaultSpinner { size = large ; overlay = true })

overlaySpinnerWithText : ∀ {M A} → String → Node M A
overlaySpinnerWithText lbl = spinnerWith (record defaultSpinner { size = large ; overlay = true ; text' = just lbl })

inlineSpinner : ∀ {M A} → Node M A
inlineSpinner = spinnerWith (record defaultSpinner { inline = true })

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
    ∷ when (not ∘ isLoading) content
    ∷ [] )
