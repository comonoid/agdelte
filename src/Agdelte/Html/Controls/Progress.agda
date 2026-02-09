{-# OPTIONS --without-K #-}

-- Progress: Progress bars, spinners, and skeleton loaders
-- CSS classes: .agdelte-progress, .agdelte-progress__bar,
--              .agdelte-spinner, .agdelte-skeleton

module Agdelte.Html.Controls.Progress where

open import Data.String using (String; _≟_)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; _≤ᵇ_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Function using (_∘_)
open import Relation.Nullary using (yes; no)

open import Agdelte.Reactive.Node

open import Agda.Builtin.String using (primShowNat)

------------------------------------------------------------------------
-- Progress bar
------------------------------------------------------------------------

-- | Progress bar with percentage value.
-- | getValue: extract current value (0-100) as string
progressBar : ∀ {M A}
            → (M → String)       -- current value as string ("0" to "100")
            → Node M A
progressBar {M} {A} getValue =
  div ( class "agdelte-progress"
      ∷ attr "role" "progressbar"
      ∷ attrBind "aria-valuenow" (mkBinding getValue eqStr)
      ∷ attr "aria-valuemin" "0"
      ∷ attr "aria-valuemax" "100"
      ∷ [] )
    ( div ( class "agdelte-progress__bar"
          ∷ styleBind "width" (mkBinding (λ m → getValue m ++ "%") eqStr)
          ∷ [] )
        []
    ∷ [] )
  where
    eqStr : String → String → Bool
    eqStr a b with a ≟ b
    ... | yes _ = true
    ... | no _  = false

    open import Data.String using (_++_)

-- | Progress bar with label
progressBarLabeled : ∀ {M A}
                   → String           -- label
                   → (M → String)     -- current value
                   → Node M A
progressBarLabeled {M} {A} lbl getValue =
  div ( class "agdelte-progress-container" ∷ [] )
    ( div ( class "agdelte-progress__header" ∷ [] )
        ( span ( class "agdelte-progress__label" ∷ [] )
            ( text lbl ∷ [] )
        ∷ span ( class "agdelte-progress__value" ∷ [] )
            ( bindF (λ m → getValue m ++ "%") ∷ [] )
        ∷ [] )
    ∷ progressBar getValue
    ∷ [] )
  where
    open import Data.String using (_++_)

-- | Indeterminate progress bar (animated, no value)
progressIndeterminate : ∀ {M A} → Node M A
progressIndeterminate =
  div ( class "agdelte-progress agdelte-progress--indeterminate"
      ∷ attr "role" "progressbar"
      ∷ [] )
    ( div ( class "agdelte-progress__bar" ∷ [] ) []
    ∷ [] )

------------------------------------------------------------------------
-- Spinner
------------------------------------------------------------------------

-- | Simple loading spinner
spinner : ∀ {M A} → Node M A
spinner = div ( class "agdelte-spinner" ∷ attr "role" "status" ∷ [] )
            ( span ( class "agdelte-spinner__sr" ∷ [] )
                ( text "Loading..." ∷ [] )
            ∷ [] )

-- | Spinner with size variant
data SpinnerSize : Set where
  Small  : SpinnerSize
  Medium : SpinnerSize
  Large  : SpinnerSize

spinnerSizeClass : SpinnerSize → String
spinnerSizeClass Small  = "agdelte-spinner--sm"
spinnerSizeClass Medium = "agdelte-spinner--md"
spinnerSizeClass Large  = "agdelte-spinner--lg"

spinnerWithSize : ∀ {M A} → SpinnerSize → Node M A
spinnerWithSize size =
  div ( class ("agdelte-spinner " ++ spinnerSizeClass size)
      ∷ attr "role" "status"
      ∷ [] )
    ( span ( class "agdelte-spinner__sr" ∷ [] )
        ( text "Loading..." ∷ [] )
    ∷ [] )
  where
    open import Data.String using (_++_)

-- | Spinner with text
spinnerWithText : ∀ {M A} → String → Node M A
spinnerWithText msg =
  div ( class "agdelte-spinner-container" ∷ [] )
    ( spinner
    ∷ span ( class "agdelte-spinner__text" ∷ [] )
        ( text msg ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- Skeleton loaders
------------------------------------------------------------------------

-- | Skeleton text line
skeletonText : ∀ {M A} → Node M A
skeletonText = div ( class "agdelte-skeleton agdelte-skeleton--text" ∷ [] ) []

-- | Skeleton circle (for avatars)
skeletonCircle : ∀ {M A} → Node M A
skeletonCircle = div ( class "agdelte-skeleton agdelte-skeleton--circle" ∷ [] ) []

-- | Skeleton rectangle (for images/cards)
skeletonRect : ∀ {M A} → String → String → Node M A
skeletonRect width height =
  div ( class "agdelte-skeleton agdelte-skeleton--rect"
      ∷ style "width" width
      ∷ style "height" height
      ∷ [] )
    []

-- | Skeleton paragraph (multiple lines)
skeletonParagraph : ∀ {M A} → ℕ → Node M A
skeletonParagraph {M} {A} lines =
  div ( class "agdelte-skeleton-paragraph" ∷ [] )
    (renderLines lines)
  where
    open import Data.Nat using (suc)

    {-# TERMINATING #-}
    renderLines : ℕ → List (Node M A)
    renderLines 0 = []
    renderLines (suc n) = skeletonText ∷ renderLines n

------------------------------------------------------------------------
-- Loading wrapper
------------------------------------------------------------------------

-- | Wrap content with loading state.
-- | When loading, shows spinner; otherwise shows content.
withLoading : ∀ {M A}
            → (M → Bool)         -- is loading
            → Node M A           -- content
            → Node M A
withLoading {M} {A} isLoading content =
  div ( class "agdelte-loading-wrapper" ∷ [] )
    ( when isLoading
        (div ( class "agdelte-loading-overlay" ∷ [] )
          ( spinner ∷ [] ))
    ∷ content
    ∷ [] )

-- | Show skeleton or content based on loading state.
withSkeleton : ∀ {M A}
             → (M → Bool)         -- is loading
             → Node M A           -- skeleton
             → Node M A           -- content
             → Node M A
withSkeleton {M} {A} isLoading skeleton content =
  div ( class "agdelte-skeleton-wrapper" ∷ [] )
    ( when isLoading skeleton
    ∷ when (not ∘ isLoading) content
    ∷ [] )
  where
    open import Data.Bool using (not)
