{-# OPTIONS --without-K #-}

-- CSS styles for the Progress, Spinner, and Skeleton controls
-- (HTML structure is in Agdelte.Html.Controls.Progress)

module Agdelte.Css.Controls.Progress where

open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)

open import Agdelte.Css.Decl using (Style; _∶_)
open import Agdelte.Css.Stylesheet using (Rule; rule; keyframe; Stylesheet)

------------------------------------------------------------------------
-- Progress rules
------------------------------------------------------------------------

progressRules : Stylesheet
progressRules =
  -- Progress bar
    rule ".agdelte-progress"
      ( "width" ∶ "100%"
      ∷ "height" ∶ "8px"
      ∷ "background" ∶ "var(--agdelte-bg-active)"
      ∷ "border-radius" ∶ "4px"
      ∷ "overflow" ∶ "hidden"
      ∷ [])
  ∷ rule ".agdelte-progress__bar"
      ( "height" ∶ "100%"
      ∷ "background" ∶ "var(--agdelte-primary)"
      ∷ "border-radius" ∶ "4px"
      ∷ "transition" ∶ "width var(--agdelte-transition)"
      ∷ [])
  ∷ rule ".agdelte-progress--indeterminate .agdelte-progress__bar"
      ( "width" ∶ "30%"
      ∷ "animation" ∶ "agdelte-progress-indeterminate 1.5s ease-in-out infinite"
      ∷ [])
  ∷ keyframe "agdelte-progress-indeterminate"
      ( ("0%"   , "transform" ∶ "translateX(-100%)" ∷ [])
      ∷ ("100%" , "transform" ∶ "translateX(400%)" ∷ [])
      ∷ [])
  ∷ rule ".agdelte-progress-container"
      ( "display" ∶ "flex"
      ∷ "flex-direction" ∶ "column"
      ∷ "gap" ∶ "var(--agdelte-spacing-xs)"
      ∷ [])
  ∷ rule ".agdelte-progress__header"
      ( "display" ∶ "flex"
      ∷ "justify-content" ∶ "space-between"
      ∷ "align-items" ∶ "center"
      ∷ [])
  ∷ rule ".agdelte-progress__label"
      ( "color" ∶ "var(--agdelte-text)"
      ∷ "font-weight" ∶ "500"
      ∷ [])
  ∷ rule ".agdelte-progress__value"
      ( "color" ∶ "var(--agdelte-text-muted)"
      ∷ "font-size" ∶ "0.875rem"
      ∷ [])
  -- Spinner
  ∷ rule ".agdelte-spinner"
      ( "display" ∶ "inline-block"
      ∷ "width" ∶ "24px"
      ∷ "height" ∶ "24px"
      ∷ "border" ∶ "2px solid var(--agdelte-border)"
      ∷ "border-top-color" ∶ "var(--agdelte-primary)"
      ∷ "border-radius" ∶ "50%"
      ∷ "animation" ∶ "agdelte-spin 0.8s linear infinite"
      ∷ [])
  ∷ rule ".agdelte-spinner--sm"
      ( "width" ∶ "16px"
      ∷ "height" ∶ "16px"
      ∷ [])
  ∷ rule ".agdelte-spinner--lg"
      ( "width" ∶ "40px"
      ∷ "height" ∶ "40px"
      ∷ "border-width" ∶ "3px"
      ∷ [])
  ∷ rule ".agdelte-spinner__sr"
      ( "position" ∶ "absolute"
      ∷ "width" ∶ "1px"
      ∷ "height" ∶ "1px"
      ∷ "padding" ∶ "0"
      ∷ "margin" ∶ "-1px"
      ∷ "overflow" ∶ "hidden"
      ∷ "clip-path" ∶ "inset(50%)"
      ∷ "white-space" ∶ "nowrap"
      ∷ "border" ∶ "0"
      ∷ [])
  ∷ rule ".agdelte-spinner-container"
      ( "display" ∶ "flex"
      ∷ "align-items" ∶ "center"
      ∷ "gap" ∶ "var(--agdelte-spacing-sm)"
      ∷ [])
  ∷ rule ".agdelte-spinner__text"
      ( "color" ∶ "var(--agdelte-text-muted)"
      ∷ [])
  ∷ keyframe "agdelte-spin"
      ( ("to" , "transform" ∶ "rotate(360deg)" ∷ [])
      ∷ [])
  -- Skeleton
  ∷ rule ".agdelte-skeleton"
      ( "background" ∶ "linear-gradient(90deg, var(--agdelte-bg-active) 25%, var(--agdelte-bg-hover) 50%, var(--agdelte-bg-active) 75%)"
      ∷ "background-size" ∶ "200% 100%"
      ∷ "animation" ∶ "agdelte-skeleton-shimmer 1.5s infinite"
      ∷ "border-radius" ∶ "var(--agdelte-border-radius)"
      ∷ [])
  ∷ rule ".agdelte-skeleton--text"
      ( "height" ∶ "1em"
      ∷ "margin-bottom" ∶ "var(--agdelte-spacing-xs)"
      ∷ [])
  ∷ rule ".agdelte-skeleton--text:last-child"
      ( "width" ∶ "70%"
      ∷ [])
  ∷ rule ".agdelte-skeleton--circle"
      ( "width" ∶ "40px"
      ∷ "height" ∶ "40px"
      ∷ "border-radius" ∶ "50%"
      ∷ [])
  ∷ rule ".agdelte-skeleton--rect"
      ( "min-height" ∶ "100px"
      ∷ [])
  ∷ rule ".agdelte-skeleton-paragraph"
      ( "display" ∶ "flex"
      ∷ "flex-direction" ∶ "column"
      ∷ [])
  ∷ keyframe "agdelte-skeleton-shimmer"
      ( ("0%"   , "background-position" ∶ "200% 0" ∷ [])
      ∷ ("100%" , "background-position" ∶ "-200% 0" ∷ [])
      ∷ [])
  -- Loading wrapper
  ∷ rule ".agdelte-loading-wrapper"
      ( "position" ∶ "relative"
      ∷ [])
  ∷ rule ".agdelte-loading-overlay"
      ( "position" ∶ "absolute"
      ∷ "top" ∶ "0"
      ∷ "right" ∶ "0"
      ∷ "bottom" ∶ "0"
      ∷ "left" ∶ "0"
      ∷ "display" ∶ "flex"
      ∷ "align-items" ∶ "center"
      ∷ "justify-content" ∶ "center"
      ∷ "background" ∶ "var(--agdelte-backdrop)"
      ∷ "z-index" ∶ "var(--agdelte-z-dropdown)"
      ∷ [])
  ∷ []
