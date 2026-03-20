{-# OPTIONS --without-K #-}

-- Slider: Range input controls
-- CSS classes: .agdelte-slider, .agdelte-slider__input,
--              .agdelte-slider__label, .agdelte-slider__value

module Agdelte.Html.Controls.Slider where

open import Data.String using (String; _++_)
open import Data.List using (List; []; _∷_) renaming (_++_ to _++ˡ_)
open import Data.Product using (_×_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool; true; false; if_then_else_)

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
-- Slider configuration (record config pattern)
------------------------------------------------------------------------

record SliderConfig (M A : Set) : Set where
  constructor mkSlider
  field
    slLabel    : Maybe String     -- Nothing → compact (no label)
    slMin      : String           -- range min bound
    slMax      : String           -- range max bound
    slStep     : Maybe String     -- Nothing → browser default
    slVertical : Bool             -- vertical orientation
    slTicks    : List String      -- tick mark values ([] → no ticks)
    slTicksId  : String           -- datalist id (used when ticks non-empty)
    slGetValue : M → String       -- read current value from model
    slFormat   : M → String       -- display formatter (often = slGetValue)
    slOnChange : Maybe (String → A) -- Nothing → disabled slider

open SliderConfig public

-- | Default slider config: labeled, horizontal, no step/ticks, enabled.
defaultSlider : ∀ {M A} → String → String → String
              → (M → String) → (String → A) → SliderConfig M A
defaultSlider lbl mn mx get onChange =
  mkSlider (just lbl) mn mx nothing false [] "" get get (just onChange)

------------------------------------------------------------------------
-- Range slider configuration
------------------------------------------------------------------------

record RangeSliderConfig (M A : Set) : Set where
  constructor mkRangeSlider
  field
    rsLabel      : Maybe String     -- Nothing → compact (no label)
    rsMin        : String           -- range bound min
    rsMax        : String           -- range bound max
    rsStep       : Maybe String     -- Nothing → browser default
    rsGetMin     : M → String       -- current min value
    rsGetMax     : M → String       -- current max value
    rsOnMinChange : String → A      -- min value change handler
    rsOnMaxChange : String → A      -- max value change handler

open RangeSliderConfig public

------------------------------------------------------------------------
-- Unified slider (config-based)
------------------------------------------------------------------------

-- | Render a slider from config. Supports all variants:
-- | label/compact, step, vertical, ticks, custom format, disabled.
sliderWith : ∀ {M A} → SliderConfig M A → Node M A
sliderWith {M} {A} cfg =
  let mm = guardMinMax (slMin cfg) (slMax cfg)
      mn = proj₁ mm
      mx = proj₂ mm
      getValue = slGetValue cfg
      formatVal = slFormat cfg
      isVert = slVertical cfg
      cls = "agdelte-slider"
            ++ (case slLabel cfg of λ where
                  nothing → " agdelte-slider--compact"
                  (just _) → "")
            ++ (if isVert then " agdelte-slider--vertical" else "")
            ++ (case slOnChange cfg of λ where
                  nothing → " agdelte-slider--disabled"
                  (just _) → "")
            ++ (case slTicks cfg of λ where
                  [] → ""
                  (_ ∷ _) → " agdelte-slider--ticks")
      labelNode : List (Node M A)
      labelNode = case slLabel cfg of λ where
        nothing → []
        (just l) → label ( class "agdelte-slider__label" ∷ [] )
                     ( text l ∷ [] ) ∷ []
      stepAttrs : List (Attr M A)
      stepAttrs = case slStep cfg of λ where
        nothing → []
        (just s) → attr "step" (guardStep s) ∷ []
      vertAttrs : List (Attr M A)
      vertAttrs = if isVert
        then style "writing-mode" "vertical-lr" ∷ []
        else []
      disabledAttrs : List (Attr M A)
      disabledAttrs = case slOnChange cfg of λ where
        nothing → attr "disabled" "true" ∷ []
        (just _) → []
      changeAttrs : List (Attr M A)
      changeAttrs = case slOnChange cfg of λ where
        nothing → []
        (just handler) → onInput handler ∷ []
      tickListAttr : List (Attr M A)
      tickListAttr = case slTicks cfg of λ where
        [] → []
        (_ ∷ _) → attr "list" (slTicksId cfg) ∷ []
      tickNodes : List (Node M A)
      tickNodes = case slTicks cfg of λ where
        [] → []
        ts → elem "datalist" ( attr "id" (slTicksId cfg) ∷ [] )
               (renderOptions ts) ∷ []
  in div ( class cls ∷ [] )
    ( labelNode
    ++ˡ ( input ( type' "range"
               ∷ class "agdelte-slider__input"
               ∷ attr "min" mn
               ∷ attr "max" mx
               ∷ valueBind getValue
               ∷ (stepAttrs ++ˡ vertAttrs ++ˡ disabledAttrs ++ˡ changeAttrs ++ˡ tickListAttr) )
        ∷ tickNodes
       ++ˡ ( span ( class "agdelte-slider__value" ∷ [] )
              ( bindF formatVal ∷ [] )
          ∷ [] )))
  where
    case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
    case x of f = f x
    renderOptions : List String → List (Node M A)
    renderOptions [] = []
    renderOptions (v ∷ vs) =
      elem "option" ( attr "value" v ∷ [] ) []
      ∷ renderOptions vs

-- | Render a range slider from config.
rangeSliderWith : ∀ {M A} → RangeSliderConfig M A → Node M A
rangeSliderWith {M} {A} cfg =
  let bb = guardMinMax (rsMin cfg) (rsMax cfg)
      mb = proj₁ bb
      xb = proj₂ bb
      getMin = rsGetMin cfg
      getMax = rsGetMax cfg
      onMinCh = rsOnMinChange cfg
      onMaxCh = rsOnMaxChange cfg
      cls = "agdelte-range-slider"
            ++ (case rsLabel cfg of λ where
                  nothing → " agdelte-range-slider--compact"
                  (just _) → "")
      labelNode : List (Node M A)
      labelNode = case rsLabel cfg of λ where
        nothing → []
        (just l) → label ( class "agdelte-range-slider__label" ∷ [] )
                     ( text l ∷ [] ) ∷ []
      stepAttrs : List (Attr M A)
      stepAttrs = case rsStep cfg of λ where
        nothing → []
        (just s) → attr "step" (guardStep s) ∷ []
  in div ( class cls ∷ [] )
    ( labelNode
    ++ˡ ( div ( class "agdelte-range-slider__container" ∷ [] )
           ( div ( class "agdelte-range-slider__track"
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
                   ∷ valueBind getMin
                   ∷ onInput onMinCh
                   ∷ stepAttrs )
           ∷ input ( type' "range"
                   ∷ class "agdelte-range-slider__input agdelte-range-slider__input--max"
                   ∷ attr "min" mb
                   ∷ attr "max" xb
                   ∷ valueBind getMax
                   ∷ onInput onMaxCh
                   ∷ stepAttrs )
           ∷ [] )
       ∷ div ( class "agdelte-range-slider__values" ∷ [] )
           ( span ( class "agdelte-range-slider__value--min" ∷ [] )
               ( bindF (λ m → clampMinStr (getMin m) (getMax m)) ∷ [] )
           ∷ span ( class "agdelte-range-slider__separator" ∷ [] )
               ( text " - " ∷ [] )
           ∷ span ( class "agdelte-range-slider__value--max" ∷ [] )
               ( bindF (λ m → clampMaxStr (getMin m) (getMax m)) ∷ [] )
           ∷ [] )
       ∷ [] ))
  where
    case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
    case x of f = f x

------------------------------------------------------------------------
-- Backward-compatible positional-args API
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
                ∷ valueBind getMin
                ∷ onInput onMinChange
                ∷ [] )
          -- Max thumb input (value clamped to not go below min)
        ∷ input ( type' "range"
                ∷ class "agdelte-range-slider__input agdelte-range-slider__input--max"
                ∷ attr "min" mb
                ∷ attr "max" xb
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
                ∷ valueBind getMin
                ∷ onInput onMinChange
                ∷ [] )
        ∷ input ( type' "range"
                ∷ class "agdelte-range-slider__input agdelte-range-slider__input--max"
                ∷ attr "min" mb
                ∷ attr "max" xb
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
                ∷ valueBind getMin
                ∷ onInput onMinChange
                ∷ [] )
        ∷ input ( type' "range"
                ∷ class "agdelte-range-slider__input agdelte-range-slider__input--max"
                ∷ attr "min" mb
                ∷ attr "max" xb
                ∷ attr "step" sv
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
