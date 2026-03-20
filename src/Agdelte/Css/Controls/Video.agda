{-# OPTIONS --without-K #-}

-- CSS styles for the Video Player control
-- (HTML structure is in Agdelte.Html.Controls.Video.*)

module Agdelte.Css.Controls.Video where

open import Data.List using (List; []; _∷_)

open import Agdelte.Css.Decl using (Style; _∶_; cursorPointer)
open import Agdelte.Css.Stylesheet using (Rule; rule; rawRule; Stylesheet)

------------------------------------------------------------------------
-- Video player rules
------------------------------------------------------------------------

videoRules : Stylesheet
videoRules =
  -- Container
    rule ".agdelte-video"
      ( "position" ∶ "relative"
      ∷ "overflow" ∶ "hidden"
      ∷ "background" ∶ "#000"
      ∷ "border-radius" ∶ "var(--agdelte-video-border-radius, 4px)"
      ∷ "width" ∶ "100%"
      ∷ "max-width" ∶ "100%"
      ∷ [])
  ∷ rule ".agdelte-video:focus-visible"
      ( "outline" ∶ "2px solid var(--agdelte-primary)"
      ∷ "outline-offset" ∶ "2px"
      ∷ [])

  -- Video element
  ∷ rule ".agdelte-video__media"
      ( "width" ∶ "100%"
      ∷ "height" ∶ "100%"
      ∷ "display" ∶ "block"
      ∷ [])

  -- Controls overlay
  ∷ rule ".agdelte-video__controls"
      ( "position" ∶ "absolute"
      ∷ "bottom" ∶ "0"
      ∷ "left" ∶ "0"
      ∷ "right" ∶ "0"
      ∷ "padding" ∶ "var(--agdelte-video-controls-padding, 8px)"
      ∷ "background" ∶ "var(--agdelte-video-controls-bg, rgba(0,0,0,0.7))"
      ∷ "color" ∶ "var(--agdelte-video-controls-color, #fff)"
      ∷ "transition" ∶ "var(--agdelte-video-controls-transition, opacity 0.3s ease)"
      ∷ "opacity" ∶ "1"
      ∷ "z-index" ∶ "2"
      ∷ [])
  ∷ rule ".agdelte-video__controls--visible"
      ( "opacity" ∶ "1"
      ∷ [])
  ∷ rule ".agdelte-video__controls--hidden"
      ( "opacity" ∶ "0"
      ∷ "pointer-events" ∶ "none"
      ∷ [])

  -- Controls layout
  ∷ rule ".agdelte-video__controls-top"
      ( "display" ∶ "flex"
      ∷ "justify-content" ∶ "space-between"
      ∷ "align-items" ∶ "center"
      ∷ "margin-bottom" ∶ "4px"
      ∷ [])
  ∷ rule ".agdelte-video__controls-bottom"
      ( "display" ∶ "flex"
      ∷ "align-items" ∶ "center"
      ∷ "gap" ∶ "8px"
      ∷ [])

  -- Slot regions (top)
  ∷ rule ".agdelte-video__slot--top-left"
      ( "display" ∶ "flex"
      ∷ "align-items" ∶ "center"
      ∷ "gap" ∶ "8px"
      ∷ [])
  ∷ rule ".agdelte-video__slot--top-center"
      ( "flex" ∶ "1"
      ∷ "display" ∶ "flex"
      ∷ "justify-content" ∶ "center"
      ∷ [])
  ∷ rule ".agdelte-video__slot--top-right"
      ( "display" ∶ "flex"
      ∷ "align-items" ∶ "center"
      ∷ "gap" ∶ "8px"
      ∷ [])

  -- Middle row (left / right side slots)
  ∷ rule ".agdelte-video__controls-middle"
      ( "display" ∶ "flex"
      ∷ "justify-content" ∶ "space-between"
      ∷ "align-items" ∶ "center"
      ∷ "flex" ∶ "1"
      ∷ [])
  ∷ rule ".agdelte-video__slot--left"
      ( "display" ∶ "flex"
      ∷ "align-items" ∶ "center"
      ∷ [])
  ∷ rule ".agdelte-video__slot--right"
      ( "display" ∶ "flex"
      ∷ "align-items" ∶ "center"
      ∷ [])

  -- Slot regions (bottom)
  ∷ rule ".agdelte-video__slot--bottom-left"
      ( "display" ∶ "flex"
      ∷ "align-items" ∶ "center"
      ∷ "gap" ∶ "8px"
      ∷ [])
  ∷ rule ".agdelte-video__slot--bottom-center"
      ( "flex" ∶ "1"
      ∷ "display" ∶ "flex"
      ∷ "align-items" ∶ "center"
      ∷ [])
  ∷ rule ".agdelte-video__slot--bottom-right"
      ( "display" ∶ "flex"
      ∷ "align-items" ∶ "center"
      ∷ "gap" ∶ "8px"
      ∷ [])

  -- Play/Pause button
  ∷ rule ".agdelte-video__play-pause"
      ( "background" ∶ "none"
      ∷ "border" ∶ "none"
      ∷ "color" ∶ "inherit"
      ∷ cursorPointer
      ∷ "padding" ∶ "4px"
      ∷ "display" ∶ "flex"
      ∷ "align-items" ∶ "center"
      ∷ [])
  ∷ rule ".agdelte-video__play-pause:focus-visible"
      ( "outline" ∶ "2px solid var(--agdelte-primary)"
      ∷ "outline-offset" ∶ "2px"
      ∷ [])

  -- Icon size
  ∷ rule ".agdelte-video__icon"
      ( "width" ∶ "var(--agdelte-video-icon-size, 24px)"
      ∷ "height" ∶ "var(--agdelte-video-icon-size, 24px)"
      ∷ "fill" ∶ "currentColor"
      ∷ [])

  -- Seek bar
  ∷ rule ".agdelte-video__seek"
      ( "position" ∶ "relative"
      ∷ "height" ∶ "var(--agdelte-video-seek-height, 4px)"
      ∷ "background" ∶ "rgba(255,255,255,0.2)"
      ∷ "border-radius" ∶ "var(--agdelte-video-border-radius, 4px)"
      ∷ cursorPointer
      ∷ "flex" ∶ "1"
      ∷ [])
  ∷ rule ".agdelte-video__seek-buffered"
      ( "position" ∶ "absolute"
      ∷ "top" ∶ "0"
      ∷ "left" ∶ "0"
      ∷ "height" ∶ "100%"
      ∷ "background" ∶ "var(--agdelte-video-buffered-color, rgba(255,255,255,0.3))"
      ∷ "border-radius" ∶ "inherit"
      ∷ "pointer-events" ∶ "none"
      ∷ [])
  ∷ rule ".agdelte-video__seek-played"
      ( "position" ∶ "absolute"
      ∷ "top" ∶ "0"
      ∷ "left" ∶ "0"
      ∷ "height" ∶ "100%"
      ∷ "background" ∶ "var(--agdelte-video-progress-color, var(--agdelte-primary))"
      ∷ "border-radius" ∶ "inherit"
      ∷ "pointer-events" ∶ "none"
      ∷ [])
  ∷ rule ".agdelte-video__seek-input"
      ( "position" ∶ "absolute"
      ∷ "top" ∶ "0"
      ∷ "left" ∶ "0"
      ∷ "width" ∶ "100%"
      ∷ "height" ∶ "100%"
      ∷ "opacity" ∶ "0"
      ∷ cursorPointer
      ∷ "margin" ∶ "0"
      ∷ [])

  -- Volume
  ∷ rule ".agdelte-video__volume"
      ( "display" ∶ "flex"
      ∷ "align-items" ∶ "center"
      ∷ "gap" ∶ "4px"
      ∷ [])
  ∷ rule ".agdelte-video__volume-icon"
      ( "background" ∶ "none"
      ∷ "border" ∶ "none"
      ∷ "color" ∶ "inherit"
      ∷ cursorPointer
      ∷ "padding" ∶ "4px"
      ∷ "display" ∶ "flex"
      ∷ "align-items" ∶ "center"
      ∷ [])
  ∷ rule ".agdelte-video__volume-icon--muted"
      ( "opacity" ∶ "0.5"
      ∷ [])
  ∷ rule ".agdelte-video__volume-slider"
      ( "width" ∶ "80px"
      ∷ "height" ∶ "4px"
      ∷ "-webkit-appearance" ∶ "none"
      ∷ "appearance" ∶ "none"
      ∷ "background" ∶ "rgba(255,255,255,0.3)"
      ∷ "border-radius" ∶ "2px"
      ∷ "accent-color" ∶ "var(--agdelte-video-controls-color, #fff)"
      ∷ [])

  -- Time display
  ∷ rule ".agdelte-video__time"
      ( "font-size" ∶ "var(--agdelte-video-font-size, 13px)"
      ∷ "font-variant-numeric" ∶ "tabular-nums"
      ∷ "white-space" ∶ "nowrap"
      ∷ "user-select" ∶ "none"
      ∷ [])

  -- Fullscreen button
  ∷ rule ".agdelte-video__fullscreen"
      ( "background" ∶ "none"
      ∷ "border" ∶ "none"
      ∷ "color" ∶ "inherit"
      ∷ cursorPointer
      ∷ "padding" ∶ "4px"
      ∷ "display" ∶ "flex"
      ∷ "align-items" ∶ "center"
      ∷ [])
  ∷ rule ".agdelte-video__fullscreen--active"
      ( "color" ∶ "var(--agdelte-primary)"
      ∷ [])
  ∷ rule ".agdelte-video__fullscreen:focus-visible"
      ( "outline" ∶ "2px solid var(--agdelte-primary)"
      ∷ "outline-offset" ∶ "2px"
      ∷ [])

  -- Rate selector
  ∷ rule ".agdelte-video__rate"
      ( "display" ∶ "flex"
      ∷ "gap" ∶ "2px"
      ∷ [])
  ∷ rule ".agdelte-video__rate-btn"
      ( "background" ∶ "none"
      ∷ "border" ∶ "1px solid rgba(255,255,255,0.3)"
      ∷ "color" ∶ "inherit"
      ∷ "font-size" ∶ "11px"
      ∷ "padding" ∶ "2px 6px"
      ∷ "border-radius" ∶ "3px"
      ∷ cursorPointer
      ∷ [])
  ∷ rule ".agdelte-video__rate-btn:hover"
      ( "background" ∶ "rgba(255,255,255,0.15)"
      ∷ [])

  -- Loading overlay
  ∷ rule ".agdelte-video__loading"
      ( "position" ∶ "absolute"
      ∷ "top" ∶ "0"
      ∷ "left" ∶ "0"
      ∷ "right" ∶ "0"
      ∷ "bottom" ∶ "0"
      ∷ "display" ∶ "flex"
      ∷ "align-items" ∶ "center"
      ∷ "justify-content" ∶ "center"
      ∷ "z-index" ∶ "1"
      ∷ "pointer-events" ∶ "none"
      ∷ [])
  ∷ rule ".agdelte-video__spinner"
      ( "width" ∶ "40px"
      ∷ "height" ∶ "40px"
      ∷ "border" ∶ "3px solid rgba(255,255,255,0.3)"
      ∷ "border-top-color" ∶ "var(--agdelte-video-controls-color, #fff)"
      ∷ "border-radius" ∶ "50%"
      ∷ "animation" ∶ "agdelte-video-spin 0.8s linear infinite"
      ∷ [])

  -- Error overlay
  ∷ rule ".agdelte-video__error"
      ( "position" ∶ "absolute"
      ∷ "top" ∶ "0"
      ∷ "left" ∶ "0"
      ∷ "right" ∶ "0"
      ∷ "bottom" ∶ "0"
      ∷ "display" ∶ "flex"
      ∷ "flex-direction" ∶ "column"
      ∷ "align-items" ∶ "center"
      ∷ "justify-content" ∶ "center"
      ∷ "gap" ∶ "8px"
      ∷ "color" ∶ "var(--agdelte-video-controls-color, #fff)"
      ∷ "font-size" ∶ "14px"
      ∷ "z-index" ∶ "3"
      ∷ "background" ∶ "rgba(0,0,0,0.8)"
      ∷ [])
  ∷ rule ".agdelte-video__error-icon"
      ( "width" ∶ "48px"
      ∷ "height" ∶ "48px"
      ∷ "border-radius" ∶ "50%"
      ∷ "border" ∶ "2px solid currentColor"
      ∷ "display" ∶ "flex"
      ∷ "align-items" ∶ "center"
      ∷ "justify-content" ∶ "center"
      ∷ "font-size" ∶ "24px"
      ∷ "font-weight" ∶ "bold"
      ∷ [])

  -- Spinner keyframes
  ∷ rawRule "@keyframes agdelte-video-spin { to { transform: rotate(360deg); } }"
  ∷ []
