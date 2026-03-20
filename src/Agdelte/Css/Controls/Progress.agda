{-# OPTIONS --without-K #-}

-- CSS styles for the Progress, Spinner, and Skeleton controls
-- (HTML structure is in Agdelte.Html.Controls.Progress)

module Agdelte.Css.Controls.Progress where

open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)

open import Agdelte.Css.Decl using (Style; _∶_; borderRadius)
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
      ∷ borderRadius
      ∷ "overflow" ∶ "hidden"
      ∷ [])
  ∷ rule ".agdelte-progress__bar"
      ( "height" ∶ "100%"
      ∷ "background" ∶ "var(--agdelte-primary)"
      ∷ borderRadius
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
  ∷ rule ".agdelte-spinner--md"
      ( "width" ∶ "32px"
      ∷ "height" ∶ "32px"
      ∷ [])
  ∷ rule ".agdelte-spinner--small"
      ( "width" ∶ "16px"
      ∷ "height" ∶ "16px"
      ∷ [])
  ∷ rule ".agdelte-spinner--large"
      ( "width" ∶ "48px"
      ∷ "height" ∶ "48px"
      ∷ "border-width" ∶ "3px"
      ∷ [])
  ∷ rule ".agdelte-spinner--inline"
      ( "vertical-align" ∶ "middle"
      ∷ [])
  ∷ rule ".agdelte-spinner-wrapper"
      ( "display" ∶ "inline-flex"
      ∷ "align-items" ∶ "center"
      ∷ "gap" ∶ "var(--agdelte-spacing-sm)"
      ∷ [])
  ∷ rule ".agdelte-spinner-overlay"
      ( "position" ∶ "absolute"
      ∷ "top" ∶ "0"
      ∷ "right" ∶ "0"
      ∷ "bottom" ∶ "0"
      ∷ "left" ∶ "0"
      ∷ "display" ∶ "flex"
      ∷ "align-items" ∶ "center"
      ∷ "justify-content" ∶ "center"
      ∷ "background" ∶ "var(--agdelte-backdrop)"
      ∷ [])
  ∷ rule ".agdelte-dot-spinner"
      ( "display" ∶ "inline-flex"
      ∷ "gap" ∶ "4px"
      ∷ "align-items" ∶ "center"
      ∷ [])
  ∷ rule ".agdelte-dot-spinner__dot"
      ( "width" ∶ "8px"
      ∷ "height" ∶ "8px"
      ∷ "border-radius" ∶ "50%"
      ∷ "background" ∶ "var(--agdelte-primary)"
      ∷ "animation" ∶ "agdelte-dot-bounce 1.4s ease-in-out infinite both"
      ∷ [])
  ∷ rule ".agdelte-pulse-spinner"
      ( "width" ∶ "24px"
      ∷ "height" ∶ "24px"
      ∷ "border-radius" ∶ "50%"
      ∷ "background" ∶ "var(--agdelte-primary)"
      ∷ "animation" ∶ "agdelte-pulse 1.5s ease-in-out infinite"
      ∷ [])
  ∷ rule ".agdelte-bar-spinner"
      ( "display" ∶ "inline-flex"
      ∷ "gap" ∶ "3px"
      ∷ "align-items" ∶ "center"
      ∷ "height" ∶ "24px"
      ∷ [])
  ∷ rule ".agdelte-bar-spinner__bar"
      ( "width" ∶ "3px"
      ∷ "height" ∶ "100%"
      ∷ "background" ∶ "var(--agdelte-primary)"
      ∷ "animation" ∶ "agdelte-bar-stretch 1.2s ease-in-out infinite"
      ∷ [])
  ∷ keyframe "agdelte-spin"
      ( ("to" , "transform" ∶ "rotate(360deg)" ∷ [])
      ∷ [])
  ∷ keyframe "agdelte-dot-bounce"
      ( ("0%, 80%, 100%" , "transform" ∶ "scale(0)" ∷ [])
      ∷ ("40%" , "transform" ∶ "scale(1)" ∷ [])
      ∷ [])
  ∷ keyframe "agdelte-pulse"
      ( ("0%" , "transform" ∶ "scale(0)" ∷ "opacity" ∶ "1" ∷ [])
      ∷ ("100%" , "transform" ∶ "scale(1)" ∷ "opacity" ∶ "0" ∷ [])
      ∷ [])
  ∷ keyframe "agdelte-bar-stretch"
      ( ("0%, 40%, 100%" , "transform" ∶ "scaleY(0.4)" ∷ [])
      ∷ ("20%" , "transform" ∶ "scaleY(1)" ∷ [])
      ∷ [])
  -- Skeleton
  ∷ rule ".agdelte-skeleton"
      ( "background" ∶ "linear-gradient(90deg, var(--agdelte-bg-active) 25%, var(--agdelte-bg-hover) 50%, var(--agdelte-bg-active) 75%)"
      ∷ "background-size" ∶ "200% 100%"
      ∷ "animation" ∶ "agdelte-skeleton-shimmer 1.5s infinite"
      ∷ borderRadius
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
  ∷ rule ".agdelte-skeleton-wrapper"
      ( "position" ∶ "relative"
      ∷ [])
  ∷ rule ".agdelte-skeleton-text"
      ( "display" ∶ "flex"
      ∷ "flex-direction" ∶ "column"
      ∷ "gap" ∶ "var(--agdelte-spacing-xs)"
      ∷ [])
  ∷ rule ".agdelte-skeleton-card"
      ( "display" ∶ "flex"
      ∷ "flex-direction" ∶ "column"
      ∷ "gap" ∶ "var(--agdelte-spacing-sm)"
      ∷ [])
  ∷ rule ".agdelte-skeleton-avatar-text"
      ( "display" ∶ "flex"
      ∷ "gap" ∶ "var(--agdelte-spacing-sm)"
      ∷ "align-items" ∶ "flex-start"
      ∷ [])
  ∷ rule ".agdelte-skeleton-table"
      ( "display" ∶ "flex"
      ∷ "flex-direction" ∶ "column"
      ∷ "gap" ∶ "var(--agdelte-spacing-xs)"
      ∷ [])
  ∷ rule ".agdelte-skeleton-list"
      ( "display" ∶ "flex"
      ∷ "flex-direction" ∶ "column"
      ∷ "gap" ∶ "var(--agdelte-spacing-sm)"
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
      ∷ "z-index" ∶ "var(--agdelte-z-modal)"
      ∷ [])
  ∷ []
