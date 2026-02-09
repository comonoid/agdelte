{-# OPTIONS --without-K #-}

-- Slider: Range input controls
-- CSS classes: .agdelte-slider, .agdelte-slider__input,
--              .agdelte-slider__label, .agdelte-slider__value

module Agdelte.Html.Controls.Slider where

open import Data.String using (String; _≟_)
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
