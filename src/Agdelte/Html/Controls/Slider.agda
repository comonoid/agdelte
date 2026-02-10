{-# OPTIONS --without-K #-}

-- Slider: Range input controls
-- CSS classes: .agdelte-slider, .agdelte-slider__input,
--              .agdelte-slider__label, .agdelte-slider__value

module Agdelte.Html.Controls.Slider where

open import Data.String using (String; _≟_; _++_)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary using (yes; no)

open import Agdelte.Reactive.Node

private
  -- String equality
  eqStr : String → String → Bool
  eqStr a b with a ≟ b
  ... | yes _ = true
  ... | no _  = false

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
  div ( class "agdelte-slider" ∷ [] )
    ( label ( class "agdelte-slider__label" ∷ [] )
        ( text lbl ∷ [] )
    ∷ input ( type' "range"
            ∷ class "agdelte-slider__input"
            ∷ attr "min" minVal
            ∷ attr "max" maxVal
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
  div ( class "agdelte-slider" ∷ [] )
    ( label ( class "agdelte-slider__label" ∷ [] )
        ( text lbl ∷ [] )
    ∷ input ( type' "range"
            ∷ class "agdelte-slider__input"
            ∷ attr "min" minVal
            ∷ attr "max" maxVal
            ∷ attr "step" stepVal
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
  div ( class "agdelte-slider agdelte-slider--compact" ∷ [] )
    ( input ( type' "range"
            ∷ class "agdelte-slider__input"
            ∷ attr "min" minVal
            ∷ attr "max" maxVal
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
  div ( class "agdelte-slider" ∷ [] )
    ( label ( class "agdelte-slider__label" ∷ [] )
        ( text lbl ∷ [] )
    ∷ input ( type' "range"
            ∷ class "agdelte-slider__input"
            ∷ attr "min" minVal
            ∷ attr "max" maxVal
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
  div ( class "agdelte-range-slider" ∷ [] )
    ( label ( class "agdelte-range-slider__label" ∷ [] )
        ( text lbl ∷ [] )
    ∷ div ( class "agdelte-range-slider__container" ∷ [] )
        ( -- Track background
          div ( class "agdelte-range-slider__track" ∷ [] ) []
          -- Min thumb input
        ∷ input ( type' "range"
                ∷ class "agdelte-range-slider__input agdelte-range-slider__input--min"
                ∷ attr "min" minBound
                ∷ attr "max" maxBound
                ∷ valueBind getMin
                ∷ onInput onMinChange
                ∷ [] )
          -- Max thumb input
        ∷ input ( type' "range"
                ∷ class "agdelte-range-slider__input agdelte-range-slider__input--max"
                ∷ attr "min" minBound
                ∷ attr "max" maxBound
                ∷ valueBind getMax
                ∷ onInput onMaxChange
                ∷ [] )
        ∷ [] )
    ∷ div ( class "agdelte-range-slider__values" ∷ [] )
        ( span ( class "agdelte-range-slider__value--min" ∷ [] )
            ( bindF getMin ∷ [] )
        ∷ span ( class "agdelte-range-slider__separator" ∷ [] )
            ( text " - " ∷ [] )
        ∷ span ( class "agdelte-range-slider__value--max" ∷ [] )
            ( bindF getMax ∷ [] )
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
  div ( class "agdelte-range-slider agdelte-range-slider--compact" ∷ [] )
    ( div ( class "agdelte-range-slider__container" ∷ [] )
        ( div ( class "agdelte-range-slider__track" ∷ [] ) []
        ∷ input ( type' "range"
                ∷ class "agdelte-range-slider__input agdelte-range-slider__input--min"
                ∷ attr "min" minBound
                ∷ attr "max" maxBound
                ∷ valueBind getMin
                ∷ onInput onMinChange
                ∷ [] )
        ∷ input ( type' "range"
                ∷ class "agdelte-range-slider__input agdelte-range-slider__input--max"
                ∷ attr "min" minBound
                ∷ attr "max" maxBound
                ∷ valueBind getMax
                ∷ onInput onMaxChange
                ∷ [] )
        ∷ [] )
    ∷ div ( class "agdelte-range-slider__values" ∷ [] )
        ( bindF (λ m → getMin m ++ " - " ++ getMax m) ∷ [] )
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
  div ( class "agdelte-range-slider" ∷ [] )
    ( label ( class "agdelte-range-slider__label" ∷ [] )
        ( text lbl ∷ [] )
    ∷ div ( class "agdelte-range-slider__container" ∷ [] )
        ( div ( class "agdelte-range-slider__track" ∷ [] ) []
        ∷ input ( type' "range"
                ∷ class "agdelte-range-slider__input agdelte-range-slider__input--min"
                ∷ attr "min" minBound
                ∷ attr "max" maxBound
                ∷ attr "step" stepVal
                ∷ valueBind getMin
                ∷ onInput onMinChange
                ∷ [] )
        ∷ input ( type' "range"
                ∷ class "agdelte-range-slider__input agdelte-range-slider__input--max"
                ∷ attr "min" minBound
                ∷ attr "max" maxBound
                ∷ attr "step" stepVal
                ∷ valueBind getMax
                ∷ onInput onMaxChange
                ∷ [] )
        ∷ [] )
    ∷ div ( class "agdelte-range-slider__values" ∷ [] )
        ( span ( class "agdelte-range-slider__value--min" ∷ [] )
            ( bindF getMin ∷ [] )
        ∷ span ( class "agdelte-range-slider__separator" ∷ [] )
            ( text " - " ∷ [] )
        ∷ span ( class "agdelte-range-slider__value--max" ∷ [] )
            ( bindF getMax ∷ [] )
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
  div ( class "agdelte-slider agdelte-slider--vertical" ∷ [] )
    ( label ( class "agdelte-slider__label" ∷ [] )
        ( text lbl ∷ [] )
    ∷ input ( type' "range"
            ∷ class "agdelte-slider__input"
            ∷ attr "min" minVal
            ∷ attr "max" maxVal
            ∷ attr "orient" "vertical"
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
  div ( class "agdelte-slider agdelte-slider--ticks" ∷ [] )
    ( label ( class "agdelte-slider__label" ∷ [] )
        ( text lbl ∷ [] )
    ∷ input ( type' "range"
            ∷ class "agdelte-slider__input"
            ∷ attr "min" minVal
            ∷ attr "max" maxVal
            ∷ attr "list" listId
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
  div ( class "agdelte-slider agdelte-slider--disabled" ∷ [] )
    ( label ( class "agdelte-slider__label" ∷ [] )
        ( text lbl ∷ [] )
    ∷ input ( type' "range"
            ∷ class "agdelte-slider__input"
            ∷ attr "min" minVal
            ∷ attr "max" maxVal
            ∷ attr "disabled" "true"
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
            ∷ valueBind getValue
            ∷ onInput onChangeMsg
            ∷ [] )
    ∷ span ( class "agdelte-slider__value" ∷ [] )
        ( bindF (λ m → getValue m ++ "%") ∷ [] )
    ∷ [] )
