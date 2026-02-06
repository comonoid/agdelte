{-# OPTIONS --without-K #-}

-- SVG Filter Helpers
-- Typed filter primitives

module Agdelte.Svg.Filter where

open import Data.Float using (Float; _*_)
open import Data.List using (List; []; _∷_)
open import Data.String using (String; _++_)
open import Agdelte.Css.Show using (showFloat)
open import Agdelte.Css.Color using (Color; showColor)
open import Agdelte.Reactive.Node using (Node; Attr; attr; elem)
open import Agdelte.Svg.Gradient using (url)

------------------------------------------------------------------------
-- Filter primitives (simplified API)
------------------------------------------------------------------------

-- Gaussian blur
feGaussianBlur : ∀ {M Msg} → String → Float → Node M Msg
feGaussianBlur input stdDev = elem "feGaussianBlur"
  ( attr "in" input
  ∷ attr "stdDeviation" (showFloat stdDev)
  ∷ []) []

-- Offset
feOffset : ∀ {M Msg} → String → Float → Float → String → Node M Msg
feOffset input dx dy result' = elem "feOffset"
  ( attr "in" input
  ∷ attr "dx" (showFloat dx)
  ∷ attr "dy" (showFloat dy)
  ∷ attr "result" result'
  ∷ []) []

-- Blend
feBlend : ∀ {M Msg} → String → String → String → Node M Msg
feBlend in1 in2 mode' = elem "feBlend"
  ( attr "in" in1
  ∷ attr "in2" in2
  ∷ attr "mode" mode'
  ∷ []) []

-- Flood (solid color)
feFlood : ∀ {M Msg} → Color → Float → String → Node M Msg
feFlood c opacity result' = elem "feFlood"
  ( attr "flood-color" (showColor c)
  ∷ attr "flood-opacity" (showFloat opacity)
  ∷ attr "result" result'
  ∷ []) []

-- Composite
feComposite : ∀ {M Msg} → String → String → String → String → Node M Msg
feComposite in1 in2 operator' result' = elem "feComposite"
  ( attr "in" in1
  ∷ attr "in2" in2
  ∷ attr "operator" operator'
  ∷ attr "result" result'
  ∷ []) []

-- Merge (combine multiple filter results)
feMerge : ∀ {M Msg} → List String → Node M Msg
feMerge inputs = elem "feMerge" []
  (map (λ s → elem "feMergeNode" (attr "in" s ∷ []) []) inputs)
  where
    open import Data.List using (map)

------------------------------------------------------------------------
-- Common filter presets
------------------------------------------------------------------------

-- Drop shadow filter definition (for use in defs)
dropShadowFilter : ∀ {M Msg} → String → Float → Float → Float → Color → Float → Node M Msg
dropShadowFilter filterId dx dy blur shadowColor opacity = elem "filter"
  ( attr "id" filterId ∷ [])
  ( feGaussianBlur "SourceAlpha" blur
  ∷ feOffset "SourceGraphic" dx dy "offsetBlur"
  ∷ feFlood shadowColor opacity "shadowColor"
  ∷ feComposite "shadowColor" "offsetBlur" "in" "shadow"
  ∷ feMerge ("shadow" ∷ "SourceGraphic" ∷ [])
  ∷ [])

-- Blur filter
blurFilter : ∀ {M Msg} → String → Float → Node M Msg
blurFilter filterId stdDev = elem "filter"
  ( attr "id" filterId ∷ [])
  ( feGaussianBlur "SourceGraphic" stdDev ∷ [])

-- Glow filter
glowFilter : ∀ {M Msg} → String → Float → Color → Node M Msg
glowFilter filterId blur glowColor = elem "filter"
  ( attr "id" filterId ∷ [])
  ( feGaussianBlur "SourceGraphic" blur
  ∷ feMerge ("SourceGraphic" ∷ [])
  ∷ [])

------------------------------------------------------------------------
-- Filter attribute helper
------------------------------------------------------------------------

-- Apply filter to element
filterAttr : ∀ {M Msg} → String → Attr M Msg
filterAttr filterId = attr "filter" (url filterId)
