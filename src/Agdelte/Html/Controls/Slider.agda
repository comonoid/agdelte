{-# OPTIONS --without-K #-}

-- Slider: Range input controls
-- CSS classes: .agdelte-slider, .agdelte-slider__input,
--              .agdelte-slider__label, .agdelte-slider__value

module Agdelte.Html.Controls.Slider where

open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; proj₁; proj₂)

open import Agdelte.Reactive.Node
open import Agdelte.Html.Controls.Util using (eqStr)

------------------------------------------------------------------------
-- Range crossover prevention (JS postulates)
------------------------------------------------------------------------

-- | Guard step value: returns "1" if input is "0" or empty, otherwise returns input
postulate guardStep : String → String
{-# COMPILE JS guardStep = function(s) {
  if (s === "" || s === "0") return "1";
  return s;
} #-}

-- | Guard min/max: if min > max (parsed as numbers), swap them
postulate guardMinMax : String → String → _×_ String String
{-# COMPILE JS guardMinMax = function(minV) { return function(maxV) {
  var a = parseFloat(minV) || 0, b = parseFloat(maxV) || 0;
  if (a > b) return { "fst": maxV, "snd": minV };
  return { "fst": minV, "snd": maxV };
}; } #-}

-- | Clamp min value to not exceed max: returns min(minVal, maxVal)
postulate clampMinStr : String → String → String
{-# COMPILE JS clampMinStr = function(minV) { return function(maxV) {
  var a = parseFloat(minV) || 0, b = parseFloat(maxV) || 0;
  return String(Math.min(a, b));
}; } #-}

-- | Clamp max value to not go below min: returns max(minVal, maxVal)
postulate clampMaxStr : String → String → String
{-# COMPILE JS clampMaxStr = function(minV) { return function(maxV) {
  var a = parseFloat(minV) || 0, b = parseFloat(maxV) || 0;
  return String(Math.max(a, b));
}; } #-}

-- | Compute percentage of value within [lo, hi] range for track highlighting
postulate rangePercent : String → String → String → String
{-# COMPILE JS rangePercent = function(lo) { return function(hi) { return function(val) {
  var l = parseFloat(lo) || 0, h = parseFloat(hi) || 0, v = parseFloat(val) || 0;
  if (h <= l) return "0";
  return String(((v - l) / (h - l)) * 100);
}; }; } #-}

------------------------------------------------------------------------
-- Basic slider (number value)
------------------------------------------------------------------------

-- | Basic slider with numeric value.
-- | lbl: label text
-- | minVal, maxVal: range bounds (as strings for HTML attrs)
-- | getValue: extract current value as string
-- | onChangeMsg: message constructor for value change
slider : ∀ {M A}
       → String              -- label
       → String              -- min
       → String              -- max
       → (M → String)        -- current value (as string)
       → (String → A)        -- change handler
       → Node M A
slider {M} {A} lbl minVal maxVal getValue onChangeMsg =
  let mm = guardMinMax minVal maxVal
      mn = proj₁ mm
      mx = proj₂ mm
  in div ( class "agdelte-slider" ∷ [] )
    ( label ( class "agdelte-slider__label" ∷ [] )
        ( text lbl ∷ [] )
    ∷ input ( type' "range"
            ∷ class "agdelte-slider__input"
            ∷ attr "min" mn
            ∷ attr "max" mx
            ∷ attr "aria-valuemin" mn
            ∷ attr "aria-valuemax" mx
            ∷ attrBind "aria-valuenow" (mkBinding getValue eqStr)
            ∷ valueBind getValue
            ∷ onInput onChangeMsg
            ∷ [] )
    ∷ span ( class "agdelte-slider__value" ∷ [] )
        ( bindF getValue ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- Slider with step
------------------------------------------------------------------------

-- | Slider with configurable step.
sliderWithStep : ∀ {M A}
               → String          -- label
               → String          -- min
               → String          -- max
               → String          -- step
               → (M → String)    -- current value
               → (String → A)    -- change handler
               → Node M A
sliderWithStep {M} {A} lbl minVal maxVal stepVal getValue onChangeMsg =
  let mm = guardMinMax minVal maxVal
      mn = proj₁ mm
      mx = proj₂ mm
      sv = guardStep stepVal
  in div ( class "agdelte-slider" ∷ [] )
    ( label ( class "agdelte-slider__label" ∷ [] )
        ( text lbl ∷ [] )
    ∷ input ( type' "range"
            ∷ class "agdelte-slider__input"
            ∷ attr "min" mn
            ∷ attr "max" mx
            ∷ attr "step" sv
            ∷ attr "aria-valuemin" mn
            ∷ attr "aria-valuemax" mx
            ∷ attrBind "aria-valuenow" (mkBinding getValue eqStr)
            ∷ valueBind getValue
            ∷ onInput onChangeMsg
            ∷ [] )
    ∷ span ( class "agdelte-slider__value" ∷ [] )
        ( bindF getValue ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- Slider without label (compact)
------------------------------------------------------------------------

-- | Compact slider without label.
sliderCompact : ∀ {M A}
              → String          -- min
              → String          -- max
              → (M → String)    -- current value
              → (String → A)    -- change handler
              → Node M A
sliderCompact {M} {A} minVal maxVal getValue onChangeMsg =
  let mm = guardMinMax minVal maxVal
      mn = proj₁ mm
      mx = proj₂ mm
  in div ( class "agdelte-slider agdelte-slider--compact" ∷ [] )
    ( input ( type' "range"
            ∷ class "agdelte-slider__input"
            ∷ attr "min" mn
            ∷ attr "max" mx
            ∷ attr "aria-valuemin" mn
            ∷ attr "aria-valuemax" mx
            ∷ attrBind "aria-valuenow" (mkBinding getValue eqStr)
            ∷ valueBind getValue
            ∷ onInput onChangeMsg
            ∷ [] )
    ∷ span ( class "agdelte-slider__value" ∷ [] )
        ( bindF getValue ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- Slider with custom value display
------------------------------------------------------------------------

-- | Slider with custom value formatting.
-- | formatValue: function to format display value
sliderWithFormat : ∀ {M A}
                 → String              -- label
                 → String              -- min
                 → String              -- max
                 → (M → String)        -- current value
                 → (M → String)        -- formatted display value
                 → (String → A)        -- change handler
                 → Node M A
sliderWithFormat {M} {A} lbl minVal maxVal getValue formatValue onChangeMsg =
  let mm = guardMinMax minVal maxVal
      mn = proj₁ mm
      mx = proj₂ mm
  in div ( class "agdelte-slider" ∷ [] )
    ( label ( class "agdelte-slider__label" ∷ [] )
        ( text lbl ∷ [] )
    ∷ input ( type' "range"
            ∷ class "agdelte-slider__input"
            ∷ attr "min" mn
            ∷ attr "max" mx
            ∷ attr "aria-valuemin" mn
            ∷ attr "aria-valuemax" mx
            ∷ attrBind "aria-valuenow" (mkBinding getValue eqStr)
            ∷ valueBind getValue
            ∷ onInput onChangeMsg
            ∷ [] )
    ∷ span ( class "agdelte-slider__value" ∷ [] )
        ( bindF formatValue ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- Range slider (dual thumb for min/max selection)
------------------------------------------------------------------------

-- | Range slider with two thumbs for selecting a range.
-- | Uses two overlapping range inputs styled to look like one slider.
-- | CSS: .agdelte-range-slider, .agdelte-range-slider__track,
-- |      .agdelte-range-slider__input--min, .agdelte-range-slider__input--max
rangeSlider : ∀ {M A}
            → String              -- label
            → String              -- min bound
            → String              -- max bound
            → (M → String)        -- current min value
            → (M → String)        -- current max value
            → (String → A)        -- on min change
            → (String → A)        -- on max change
            → Node M A
rangeSlider {M} {A} lbl minBound maxBound getMin getMax onMinChange onMaxChange =
  let bb = guardMinMax minBound maxBound
      mb = proj₁ bb
      xb = proj₂ bb
  in div ( class "agdelte-range-slider" ∷ [] )
    ( label ( class "agdelte-range-slider__label" ∷ [] )
        ( text lbl ∷ [] )
    ∷ div ( class "agdelte-range-slider__container" ∷ [] )
        ( -- Track background with clamped width to visualize selected range
          div ( class "agdelte-range-slider__track"
              ∷ styleBind "width" (mkBinding
                  (λ m → let clMin = clampMinStr (getMin m) (getMax m)
                             clMax = clampMaxStr (getMin m) (getMax m)
                         in rangePercent mb xb clMax
                            ++ "%")
                  eqStr)
              ∷ styleBind "margin-left" (mkBinding
                  (λ m → rangePercent mb xb
                            (clampMinStr (getMin m) (getMax m))
                         ++ "%")
                  eqStr)
              ∷ [] ) []
          -- Min thumb input (value clamped to not exceed max)
        ∷ input ( type' "range"
                ∷ class "agdelte-range-slider__input agdelte-range-slider__input--min"
                ∷ attr "min" mb
                ∷ attr "max" xb
                ∷ attr "aria-valuemin" mb
                ∷ attr "aria-valuemax" xb
                ∷ attrBind "aria-valuenow" (mkBinding
                    (λ m → clampMinStr (getMin m) (getMax m)) eqStr)
                ∷ attr "aria-label" "Range minimum"
                ∷ valueBind getMin
                ∷ onInput onMinChange
                ∷ [] )
          -- Max thumb input (value clamped to not go below min)
        ∷ input ( type' "range"
                ∷ class "agdelte-range-slider__input agdelte-range-slider__input--max"
                ∷ attr "min" mb
                ∷ attr "max" xb
                ∷ attr "aria-valuemin" mb
                ∷ attr "aria-valuemax" xb
                ∷ attrBind "aria-valuenow" (mkBinding
                    (λ m → clampMaxStr (getMin m) (getMax m)) eqStr)
                ∷ attr "aria-label" "Range maximum"
                ∷ valueBind getMax
                ∷ onInput onMaxChange
                ∷ [] )
        ∷ [] )
    ∷ div ( class "agdelte-range-slider__values" ∷ [] )
        ( span ( class "agdelte-range-slider__value--min" ∷ [] )
            ( bindF (λ m → clampMinStr (getMin m) (getMax m)) ∷ [] )
        ∷ span ( class "agdelte-range-slider__separator" ∷ [] )
            ( text " - " ∷ [] )
        ∷ span ( class "agdelte-range-slider__value--max" ∷ [] )
            ( bindF (λ m → clampMaxStr (getMin m) (getMax m)) ∷ [] )
        ∷ [] )
    ∷ [] )

-- | Range slider without label (compact).
rangeSliderCompact : ∀ {M A}
                   → String          -- min bound
                   → String          -- max bound
                   → (M → String)    -- current min value
                   → (M → String)    -- current max value
                   → (String → A)    -- on min change
                   → (String → A)    -- on max change
                   → Node M A
rangeSliderCompact {M} {A} minBound maxBound getMin getMax onMinChange onMaxChange =
  let bb = guardMinMax minBound maxBound
      mb = proj₁ bb
      xb = proj₂ bb
  in div ( class "agdelte-range-slider agdelte-range-slider--compact" ∷ [] )
    ( div ( class "agdelte-range-slider__container" ∷ [] )
        ( -- Track with clamped width to visualize selected range
          div ( class "agdelte-range-slider__track"
              ∷ styleBind "width" (mkBinding
                  (λ m → let clMin = clampMinStr (getMin m) (getMax m)
                             clMax = clampMaxStr (getMin m) (getMax m)
                         in rangePercent mb xb clMax
                            ++ "%")
                  eqStr)
              ∷ styleBind "margin-left" (mkBinding
                  (λ m → rangePercent mb xb
                            (clampMinStr (getMin m) (getMax m))
                         ++ "%")
                  eqStr)
              ∷ [] ) []
        ∷ input ( type' "range"
                ∷ class "agdelte-range-slider__input agdelte-range-slider__input--min"
                ∷ attr "min" mb
                ∷ attr "max" xb
                ∷ attr "aria-valuemin" mb
                ∷ attr "aria-valuemax" xb
                ∷ attrBind "aria-valuenow" (mkBinding
                    (λ m → clampMinStr (getMin m) (getMax m)) eqStr)
                ∷ attr "aria-label" "Range minimum"
                ∷ valueBind getMin
                ∷ onInput onMinChange
                ∷ [] )
        ∷ input ( type' "range"
                ∷ class "agdelte-range-slider__input agdelte-range-slider__input--max"
                ∷ attr "min" mb
                ∷ attr "max" xb
                ∷ attr "aria-valuemin" mb
                ∷ attr "aria-valuemax" xb
                ∷ attrBind "aria-valuenow" (mkBinding
                    (λ m → clampMaxStr (getMin m) (getMax m)) eqStr)
                ∷ attr "aria-label" "Range maximum"
                ∷ valueBind getMax
                ∷ onInput onMaxChange
                ∷ [] )
        ∷ [] )
    ∷ div ( class "agdelte-range-slider__values" ∷ [] )
        ( span ( class "agdelte-range-slider__value--min" ∷ [] )
            ( bindF (λ m → clampMinStr (getMin m) (getMax m)) ∷ [] )
        ∷ span ( class "agdelte-range-slider__separator" ∷ [] )
            ( text " - " ∷ [] )
        ∷ span ( class "agdelte-range-slider__value--max" ∷ [] )
            ( bindF (λ m → clampMaxStr (getMin m) (getMax m)) ∷ [] )
        ∷ [] )
    ∷ [] )

-- | Range slider with step value.
rangeSliderWithStep : ∀ {M A}
                    → String          -- label
                    → String          -- min bound
                    → String          -- max bound
                    → String          -- step
                    → (M → String)    -- current min value
                    → (M → String)    -- current max value
                    → (String → A)    -- on min change
                    → (String → A)    -- on max change
                    → Node M A
rangeSliderWithStep {M} {A} lbl minBound maxBound stepVal getMin getMax onMinChange onMaxChange =
  let bb = guardMinMax minBound maxBound
      mb = proj₁ bb
      xb = proj₂ bb
      sv = guardStep stepVal
  in div ( class "agdelte-range-slider" ∷ [] )
    ( label ( class "agdelte-range-slider__label" ∷ [] )
        ( text lbl ∷ [] )
    ∷ div ( class "agdelte-range-slider__container" ∷ [] )
        ( -- Track with clamped width to visualize selected range
          div ( class "agdelte-range-slider__track"
              ∷ styleBind "width" (mkBinding
                  (λ m → let clMax = clampMaxStr (getMin m) (getMax m)
                         in rangePercent mb xb clMax ++ "%")
                  eqStr)
              ∷ styleBind "margin-left" (mkBinding
                  (λ m → rangePercent mb xb
                            (clampMinStr (getMin m) (getMax m))
                         ++ "%")
                  eqStr)
              ∷ [] ) []
        ∷ input ( type' "range"
                ∷ class "agdelte-range-slider__input agdelte-range-slider__input--min"
                ∷ attr "min" mb
                ∷ attr "max" xb
                ∷ attr "step" sv
                ∷ attr "aria-valuemin" mb
                ∷ attr "aria-valuemax" xb
                ∷ attrBind "aria-valuenow" (mkBinding
                    (λ m → clampMinStr (getMin m) (getMax m)) eqStr)
                ∷ attr "aria-label" "Range minimum"
                ∷ valueBind getMin
                ∷ onInput onMinChange
                ∷ [] )
        ∷ input ( type' "range"
                ∷ class "agdelte-range-slider__input agdelte-range-slider__input--max"
                ∷ attr "min" mb
                ∷ attr "max" xb
                ∷ attr "step" sv
                ∷ attr "aria-valuemin" mb
                ∷ attr "aria-valuemax" xb
                ∷ attrBind "aria-valuenow" (mkBinding
                    (λ m → clampMaxStr (getMin m) (getMax m)) eqStr)
                ∷ attr "aria-label" "Range maximum"
                ∷ valueBind getMax
                ∷ onInput onMaxChange
                ∷ [] )
        ∷ [] )
    ∷ div ( class "agdelte-range-slider__values" ∷ [] )
        ( span ( class "agdelte-range-slider__value--min" ∷ [] )
            ( bindF (λ m → clampMinStr (getMin m) (getMax m)) ∷ [] )
        ∷ span ( class "agdelte-range-slider__separator" ∷ [] )
            ( text " - " ∷ [] )
        ∷ span ( class "agdelte-range-slider__value--max" ∷ [] )
            ( bindF (λ m → clampMaxStr (getMin m) (getMax m)) ∷ [] )
        ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- Vertical slider
------------------------------------------------------------------------

-- | Vertical slider.
sliderVertical : ∀ {M A}
               → String              -- label
               → String              -- min
               → String              -- max
               → (M → String)        -- current value
               → (String → A)        -- change handler
               → Node M A
sliderVertical {M} {A} lbl minVal maxVal getValue onChangeMsg =
  let mm = guardMinMax minVal maxVal
      mn = proj₁ mm
      mx = proj₂ mm
  in div ( class "agdelte-slider agdelte-slider--vertical" ∷ [] )
    ( label ( class "agdelte-slider__label" ∷ [] )
        ( text lbl ∷ [] )
    ∷ input ( type' "range"
            ∷ class "agdelte-slider__input"
            ∷ attr "min" mn
            ∷ attr "max" mx
            ∷ style "writing-mode" "vertical-lr"
            ∷ attr "aria-orientation" "vertical"
            ∷ attr "aria-valuemin" mn
            ∷ attr "aria-valuemax" mx
            ∷ attrBind "aria-valuenow" (mkBinding getValue eqStr)
            ∷ valueBind getValue
            ∷ onInput onChangeMsg
            ∷ [] )
    ∷ span ( class "agdelte-slider__value" ∷ [] )
        ( bindF getValue ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- Slider with tick marks
------------------------------------------------------------------------

-- | Slider with visible tick marks using datalist.
sliderWithTicks : ∀ {M A}
                → String              -- label
                → String              -- min
                → String              -- max
                → List String         -- tick values
                → String              -- datalist id
                → (M → String)        -- current value
                → (String → A)        -- change handler
                → Node M A
sliderWithTicks {M} {A} lbl minVal maxVal ticks listId getValue onChangeMsg =
  let mm = guardMinMax minVal maxVal
      mn = proj₁ mm
      mx = proj₂ mm
  in div ( class "agdelte-slider agdelte-slider--ticks" ∷ [] )
    ( label ( class "agdelte-slider__label" ∷ [] )
        ( text lbl ∷ [] )
    ∷ input ( type' "range"
            ∷ class "agdelte-slider__input"
            ∷ attr "min" mn
            ∷ attr "max" mx
            ∷ attr "list" listId
            ∷ attr "aria-valuemin" mn
            ∷ attr "aria-valuemax" mx
            ∷ attrBind "aria-valuenow" (mkBinding getValue eqStr)
            ∷ valueBind getValue
            ∷ onInput onChangeMsg
            ∷ [] )
    ∷ elem "datalist" ( attr "id" listId ∷ [] )
        (renderOptions ticks)
    ∷ span ( class "agdelte-slider__value" ∷ [] )
        ( bindF getValue ∷ [] )
    ∷ [] )
  where
    renderOptions : List String → List (Node M A)
    renderOptions [] = []
    renderOptions (v ∷ vs) =
      elem "option" ( attr "value" v ∷ [] ) []
      ∷ renderOptions vs

------------------------------------------------------------------------
-- Disabled slider
------------------------------------------------------------------------

-- | Disabled slider (read-only display).
sliderDisabled : ∀ {M A}
               → String              -- label
               → String              -- min
               → String              -- max
               → (M → String)        -- current value
               → Node M A
sliderDisabled {M} {A} lbl minVal maxVal getValue =
  let mm = guardMinMax minVal maxVal
      mn = proj₁ mm
      mx = proj₂ mm
  in div ( class "agdelte-slider agdelte-slider--disabled" ∷ [] )
    ( label ( class "agdelte-slider__label" ∷ [] )
        ( text lbl ∷ [] )
    ∷ input ( type' "range"
            ∷ class "agdelte-slider__input"
            ∷ attr "min" mn
            ∷ attr "max" mx
            ∷ attr "disabled" "true"
            ∷ attr "aria-valuemin" mn
            ∷ attr "aria-valuemax" mx
            ∷ attrBind "aria-valuenow" (mkBinding getValue eqStr)
            ∷ valueBind getValue
            ∷ [] )
    ∷ span ( class "agdelte-slider__value" ∷ [] )
        ( bindF getValue ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- Color slider (hue selector)
------------------------------------------------------------------------

-- | Hue slider for color selection (0-360).
hueSlider : ∀ {M A}
          → String              -- label
          → (M → String)        -- current hue value
          → (String → A)        -- change handler
          → Node M A
hueSlider {M} {A} lbl getValue onChangeMsg =
  div ( class "agdelte-slider agdelte-slider--hue" ∷ [] )
    ( label ( class "agdelte-slider__label" ∷ [] )
        ( text lbl ∷ [] )
    ∷ input ( type' "range"
            ∷ class "agdelte-slider__input"
            ∷ attr "min" "0"
            ∷ attr "max" "360"
            ∷ attr "aria-valuemin" "0"
            ∷ attr "aria-valuemax" "360"
            ∷ attrBind "aria-valuenow" (mkBinding getValue eqStr)
            ∷ valueBind getValue
            ∷ onInput onChangeMsg
            ∷ [] )
    ∷ span ( class "agdelte-slider__value" ∷ [] )
        ( bindF (λ m → getValue m ++ "°") ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- Percentage slider
------------------------------------------------------------------------

-- | Percentage slider (0-100).
percentSlider : ∀ {M A}
              → String              -- label
              → (M → String)        -- current value (0-100)
              → (String → A)        -- change handler
              → Node M A
percentSlider {M} {A} lbl getValue onChangeMsg =
  div ( class "agdelte-slider agdelte-slider--percent" ∷ [] )
    ( label ( class "agdelte-slider__label" ∷ [] )
        ( text lbl ∷ [] )
    ∷ input ( type' "range"
            ∷ class "agdelte-slider__input"
            ∷ attr "min" "0"
            ∷ attr "max" "100"
            ∷ attr "aria-valuemin" "0"
            ∷ attr "aria-valuemax" "100"
            ∷ attrBind "aria-valuenow" (mkBinding getValue eqStr)
            ∷ valueBind getValue
            ∷ onInput onChangeMsg
            ∷ [] )
    ∷ span ( class "agdelte-slider__value" ∷ [] )
        ( bindF (λ m → getValue m ++ "%") ∷ [] )
    ∷ [] )
