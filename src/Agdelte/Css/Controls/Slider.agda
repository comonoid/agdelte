{-# OPTIONS --without-K #-}

-- CSS styles for the Slider control
-- (HTML structure is in Agdelte.Html.Controls.Slider)

module Agdelte.Css.Controls.Slider where

open import Data.List using (List; []; _∷_)

open import Agdelte.Css.Decl using (Style; _∶_)
open import Agdelte.Css.Stylesheet using (Rule; rule; Stylesheet)

------------------------------------------------------------------------
-- Slider rules
------------------------------------------------------------------------

sliderRules : Stylesheet
sliderRules =
  -- Base slider
    rule ".agdelte-slider"
      ( "display" ∶ "flex"
      ∷ "flex-direction" ∶ "column"
      ∷ "gap" ∶ "var(--agdelte-spacing-xs)"
      ∷ [])
  ∷ rule ".agdelte-slider--compact"
      ( "flex-direction" ∶ "row"
      ∷ "align-items" ∶ "center"
      ∷ "gap" ∶ "var(--agdelte-spacing-sm)"
      ∷ [])
  ∷ rule ".agdelte-slider__label"
      ( "color" ∶ "var(--agdelte-text)"
      ∷ "font-weight" ∶ "500"
      ∷ [])
  ∷ rule ".agdelte-slider__input"
      ( "width" ∶ "100%"
      ∷ "height" ∶ "6px"
      ∷ "cursor" ∶ "pointer"
      ∷ "accent-color" ∶ "var(--agdelte-primary)"
      ∷ "-webkit-appearance" ∶ "none"
      ∷ "appearance" ∶ "none"
      ∷ "background" ∶ "var(--agdelte-border)"
      ∷ "border-radius" ∶ "var(--agdelte-border-radius)"
      ∷ [])
  ∷ rule ".agdelte-slider__input:focus-visible"
      ( "outline" ∶ "2px solid var(--agdelte-primary)"
      ∷ "outline-offset" ∶ "2px"
      ∷ [])
  ∷ rule ".agdelte-slider__input::-webkit-slider-thumb"
      ( "-webkit-appearance" ∶ "none"
      ∷ "width" ∶ "18px"
      ∷ "height" ∶ "18px"
      ∷ "background" ∶ "var(--agdelte-primary)"
      ∷ "border-radius" ∶ "50%"
      ∷ "cursor" ∶ "pointer"
      ∷ "transition" ∶ "transform var(--agdelte-transition)"
      ∷ [])
  ∷ rule ".agdelte-slider__input::-webkit-slider-thumb:hover"
      ( "transform" ∶ "scale(1.1)"
      ∷ [])
  ∷ rule ".agdelte-slider__input::-moz-range-thumb"
      ( "width" ∶ "18px"
      ∷ "height" ∶ "18px"
      ∷ "background" ∶ "var(--agdelte-primary)"
      ∷ "border" ∶ "none"
      ∷ "border-radius" ∶ "50%"
      ∷ "cursor" ∶ "pointer"
      ∷ [])
  ∷ rule ".agdelte-slider__input::-moz-range-track"
      ( "background" ∶ "var(--agdelte-border)"
      ∷ "border-radius" ∶ "var(--agdelte-border-radius)"
      ∷ "height" ∶ "6px"
      ∷ [])
  ∷ rule ".agdelte-slider__value"
      ( "color" ∶ "var(--agdelte-text)"
      ∷ "font-weight" ∶ "500"
      ∷ "min-width" ∶ "40px"
      ∷ "text-align" ∶ "center"
      ∷ [])
  ∷ rule ".agdelte-slider--compact .agdelte-slider__input"
      ( "flex" ∶ "1"
      ∷ "max-width" ∶ "200px"
      ∷ [])
  -- Vertical slider
  ∷ rule ".agdelte-slider--vertical"
      ( "align-items" ∶ "center"
      ∷ "height" ∶ "200px"
      ∷ [])
  ∷ rule ".agdelte-slider--vertical .agdelte-slider__input"
      ( "writing-mode" ∶ "vertical-lr"
      ∷ "direction" ∶ "rtl"
      ∷ "width" ∶ "6px"
      ∷ "height" ∶ "100%"
      ∷ [])
  -- Disabled slider
  ∷ rule ".agdelte-slider--disabled"
      ( "opacity" ∶ "0.5"
      ∷ "pointer-events" ∶ "none"
      ∷ [])
  -- Hue slider
  ∷ rule ".agdelte-slider--hue .agdelte-slider__input"
      ( "background" ∶ "linear-gradient(to right, hsl(0, 100%, 50%), hsl(60, 100%, 50%), hsl(120, 100%, 50%), hsl(180, 100%, 50%), hsl(240, 100%, 50%), hsl(300, 100%, 50%), hsl(360, 100%, 50%))"
      ∷ [])
  -- Percent slider
  ∷ rule ".agdelte-slider--percent .agdelte-slider__value::after"
      ( "content" ∶ "\"%\""
      ∷ [])
  -- Range Slider (dual thumb)
  ∷ rule ".agdelte-range-slider"
      ( "display" ∶ "flex"
      ∷ "flex-direction" ∶ "column"
      ∷ "gap" ∶ "var(--agdelte-spacing-xs)"
      ∷ [])
  ∷ rule ".agdelte-range-slider__label"
      ( "color" ∶ "var(--agdelte-text)"
      ∷ "font-weight" ∶ "500"
      ∷ [])
  ∷ rule ".agdelte-range-slider__container"
      ( "position" ∶ "relative"
      ∷ "height" ∶ "24px"
      ∷ [])
  ∷ rule ".agdelte-range-slider__track"
      ( "position" ∶ "absolute"
      ∷ "top" ∶ "50%"
      ∷ "left" ∶ "0"
      ∷ "right" ∶ "0"
      ∷ "height" ∶ "6px"
      ∷ "transform" ∶ "translateY(-50%)"
      ∷ "background" ∶ "var(--agdelte-border)"
      ∷ "border-radius" ∶ "var(--agdelte-border-radius)"
      ∷ "pointer-events" ∶ "none"
      ∷ [])
  ∷ rule ".agdelte-range-slider__input"
      ( "position" ∶ "absolute"
      ∷ "top" ∶ "0"
      ∷ "left" ∶ "0"
      ∷ "width" ∶ "100%"
      ∷ "height" ∶ "100%"
      ∷ "-webkit-appearance" ∶ "none"
      ∷ "appearance" ∶ "none"
      ∷ "background" ∶ "transparent"
      ∷ "pointer-events" ∶ "none"
      ∷ [])
  ∷ rule ".agdelte-range-slider__input::-webkit-slider-thumb"
      ( "-webkit-appearance" ∶ "none"
      ∷ "width" ∶ "18px"
      ∷ "height" ∶ "18px"
      ∷ "background" ∶ "var(--agdelte-primary)"
      ∷ "border-radius" ∶ "50%"
      ∷ "cursor" ∶ "pointer"
      ∷ "pointer-events" ∶ "auto"
      ∷ [])
  ∷ rule ".agdelte-range-slider__input::-moz-range-thumb"
      ( "width" ∶ "18px"
      ∷ "height" ∶ "18px"
      ∷ "background" ∶ "var(--agdelte-primary)"
      ∷ "border" ∶ "none"
      ∷ "border-radius" ∶ "50%"
      ∷ "cursor" ∶ "pointer"
      ∷ "pointer-events" ∶ "auto"
      ∷ [])
  ∷ rule ".agdelte-range-slider__values"
      ( "display" ∶ "flex"
      ∷ "justify-content" ∶ "space-between"
      ∷ "color" ∶ "var(--agdelte-text)"
      ∷ "font-size" ∶ "0.875rem"
      ∷ [])
  ∷ rule ".agdelte-range-slider__separator"
      ( "color" ∶ "var(--agdelte-text-muted)"
      ∷ [])
  ∷ rule ".agdelte-range-slider--compact"
      ( "flex-direction" ∶ "row"
      ∷ "align-items" ∶ "center"
      ∷ "gap" ∶ "var(--agdelte-spacing-sm)"
      ∷ [])
  ∷ rule ".agdelte-range-slider--compact .agdelte-range-slider__container"
      ( "flex" ∶ "1"
      ∷ "max-width" ∶ "200px"
      ∷ [])
  ∷ []
