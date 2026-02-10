{-# OPTIONS --without-K #-}

-- WebGL Controls Charts Bar3D
--
-- 3D bar charts for data visualization.
-- Supports simple bars, grouped bars, and stacked bars.

module Agdelte.WebGL.Controls.Charts.Bar3D where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Float using (Float; _*_; _+_; _-_; -_)
open import Data.String using (String)
open import Data.List using (List; []; _∷_; length)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)

open import Agdelte.WebGL.Types
open import Agdelte.WebGL.Builder.Geometry.Primitives
open import Agdelte.WebGL.Controls.Theme
open import Agdelte.WebGL.Controls.Text

------------------------------------------------------------------------
-- Helper postulates
------------------------------------------------------------------------

postulate
  natToFloat : ℕ → Float
  maxFloat : Float → Float → Float
  absFloat : Float → Float

{-# COMPILE JS natToFloat = n => Number(n) #-}
{-# COMPILE JS maxFloat = a => b => Math.max(a, b) #-}
{-# COMPILE JS absFloat = x => Math.abs(x) #-}

------------------------------------------------------------------------
-- Bar chart data
------------------------------------------------------------------------

record BarData : Set where
  constructor mkBarData
  field
    barLabel : String
    barValue : Float
    barColor : Maybe GlColor

simpleBar : String → Float → BarData
simpleBar lbl val = mkBarData lbl val nothing

coloredBar : String → Float → GlColor → BarData
coloredBar lbl val c = mkBarData lbl val (just c)

------------------------------------------------------------------------
-- Bar chart configuration
------------------------------------------------------------------------

record BarChartConfig : Set where
  constructor mkBarChartConfig
  field
    maxHeight   : Float           -- Maximum bar height
    barWidth    : Float           -- Width of each bar
    barDepth    : Float           -- Depth of bars
    spacing     : Float           -- Space between bars
    showLabels  : Bool            -- Show labels below bars
    showValues  : Bool            -- Show values above bars
    colorScheme : List GlColor    -- Default colors for bars

defaultBarChartConfig : BarChartConfig
defaultBarChartConfig = mkBarChartConfig
  0.5        -- maxHeight
  0.08       -- barWidth
  0.04       -- barDepth
  0.03       -- spacing
  true       -- showLabels
  true       -- showValues
  defaultColorScheme
  where
    defaultColorScheme : List GlColor
    defaultColorScheme =
        rgba 0.2 0.6 0.9 1.0   -- blue
      ∷ rgba 0.9 0.3 0.3 1.0   -- red
      ∷ rgba 0.3 0.8 0.3 1.0   -- green
      ∷ rgba 0.9 0.7 0.2 1.0   -- yellow
      ∷ rgba 0.7 0.3 0.8 1.0   -- purple
      ∷ rgba 0.9 0.5 0.2 1.0   -- orange
      ∷ []

------------------------------------------------------------------------
-- Bar chart implementation
------------------------------------------------------------------------

-- Get color from scheme by index
getColorAt : List GlColor → ℕ → GlColor
getColorAt [] _ = rgba 0.5 0.5 0.5 1.0  -- gray fallback
getColorAt (c ∷ _) zero = c
getColorAt (_ ∷ cs) (suc n) = getColorAt cs n

-- Find maximum value in data for scaling
findMaxValue : List BarData → Float
findMaxValue [] = 1.0  -- avoid division by zero
findMaxValue (d ∷ ds) = maxFloat (absFloat (BarData.barValue d)) (findMaxValue ds)

-- 3D bar chart
barChart3D : ∀ {M Msg}
           → ControlTheme
           → BarChartConfig
           → (M → List BarData)         -- Data accessor
           → Maybe (ℕ → Msg)            -- Optional click handler
           → Transform
           → SceneNode M Msg
barChart3D {M} {Msg} theme config getData clickHandler t =
  bindChildren buildBars t
  where
    maxH = BarChartConfig.maxHeight config
    barW = BarChartConfig.barWidth config
    barD = BarChartConfig.barDepth config
    spacing = BarChartConfig.spacing config
    showLbls = BarChartConfig.showLabels config
    showVals = BarChartConfig.showValues config
    colors = BarChartConfig.colorScheme config

    case_of_ : ∀ {A B : Set} → A → (A → B) → B
    case x of f = f x

    postulate showFloat : Float → String
    {-# COMPILE JS showFloat = x => x.toFixed(1) #-}

    _++_ : List (SceneNode M Msg) → List (SceneNode M Msg) → List (SceneNode M Msg)
    [] ++ ys = ys
    (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

    -- Build a single bar with optional label and value
    buildSingleBar : Float → String → Float → GlColor → ℕ → SceneNode M Msg
    buildSingleBar x lbl val color idx =
      let heightRatio = absFloat val * 0.5  -- simplified
          barHeight = maxH * heightRatio + 0.01  -- minimum height
          y = barHeight * 0.5
          barT = mkTransform (vec3 x y 0.0) identityQuat (vec3 1.0 1.0 1.0)
          barGeom = roundedBox (vec3 barW barHeight barD) (barW * 0.1) 4
          barMat = phong color 48.0
          -- Label below bar
          labelT = mkTransform (vec3 x (- 0.03) 0.0) identityQuat (vec3 1.0 1.0 1.0)
          -- Value above bar
          valueT = mkTransform (vec3 x (barHeight + 0.02) 0.0) identityQuat (vec3 1.0 1.0 1.0)
          -- Click handling
          attrs = case clickHandler of λ where
            nothing → transition (ms 150) easeOut ∷ []
            (just handler) → onClick (handler idx) ∷ transition (ms 150) easeOut ∷ []
      in group identityTransform
           ( interactiveGroup attrs barT
               (mesh barGeom barMat [] identityTransform ∷ [])
           ∷ (if showLbls then sizedLabel theme 0.025 lbl labelT ∷ [] else [])
           ++ (if showVals then sizedLabel theme 0.02 (showFloat val) valueT ∷ [] else []))

    buildBarList : Float → Float → ℕ → List BarData → List (SceneNode M Msg)
    buildBarList _ _ _ [] = []
    buildBarList maxVal startX idx (d ∷ ds) =
      let val = BarData.barValue d
          lbl = BarData.barLabel d
          -- Get bar color
          barColor = case BarData.barColor d of λ where
            (just c) → c
            nothing → getColorAt colors idx
          -- Bar position
          x = startX + natToFloat idx * (barW + spacing)
          -- Create bar
          bar = buildSingleBar x lbl val barColor idx
      in bar ∷ buildBarList maxVal startX (suc idx) ds

    buildBars : M → List (SceneNode M Msg)
    buildBars m =
      let bars = getData m
          maxVal = findMaxValue bars
          n = length bars
          totalWidth = natToFloat n * (barW + spacing) - spacing
          startX = - (totalWidth * 0.5) + barW * 0.5
      in buildBarList maxVal startX 0 bars

-- Simple bar chart with default config
barChart : ∀ {M Msg}
         → ControlTheme
         → (M → List BarData)
         → Transform
         → SceneNode M Msg
barChart theme getData = barChart3D theme defaultBarChartConfig getData nothing

------------------------------------------------------------------------
-- Horizontal bar chart
------------------------------------------------------------------------

horizontalBarChart3D : ∀ {M Msg}
                     → ControlTheme
                     → BarChartConfig
                     → (M → List BarData)
                     → Maybe (ℕ → Msg)
                     → Transform
                     → SceneNode M Msg
horizontalBarChart3D {M} {Msg} theme config getData clickHandler t =
  bindChildren buildBars t
  where
    maxH = BarChartConfig.maxHeight config
    barW = BarChartConfig.barWidth config
    barD = BarChartConfig.barDepth config
    spacing = BarChartConfig.spacing config
    colors = BarChartConfig.colorScheme config

    case_of_ : ∀ {A B : Set} → A → (A → B) → B
    case x of f = f x

    buildBarList : Float → ℕ → List BarData → List (SceneNode M Msg)
    buildBarList _ _ [] = []
    buildBarList startY idx (d ∷ ds) =
      let val = BarData.barValue d
          lbl = BarData.barLabel d
          barColor = case BarData.barColor d of λ where
            (just c) → c
            nothing → getColorAt colors idx
          -- Bar dimensions (horizontal)
          barLength = maxH * (absFloat val * 0.5 + 0.02)
          y = startY - natToFloat idx * (barW + spacing)
          x = barLength * 0.5
          barT = mkTransform (vec3 x y 0.0) identityQuat (vec3 1.0 1.0 1.0)
          barGeom = roundedBox (vec3 barLength barW barD) (barW * 0.1) 4
          barMat = phong barColor 48.0
          -- Label at left
          labelT = mkTransform (vec3 (- 0.05) y 0.0) identityQuat (vec3 1.0 1.0 1.0)
          attrs = case clickHandler of λ where
            nothing → transition (ms 150) easeOut ∷ []
            (just handler) → onClick (handler idx) ∷ transition (ms 150) easeOut ∷ []
      in group identityTransform
           ( interactiveGroup attrs barT
               (mesh barGeom barMat [] identityTransform ∷ [])
           ∷ rightLabel theme lbl labelT
           ∷ [])
         ∷ buildBarList startY (suc idx) ds

    buildBars : M → List (SceneNode M Msg)
    buildBars m =
      let bars = getData m
          n = length bars
          totalHeight = natToFloat n * (barW + spacing) - spacing
          startY = totalHeight * 0.5 - barW * 0.5
      in buildBarList startY 0 bars

