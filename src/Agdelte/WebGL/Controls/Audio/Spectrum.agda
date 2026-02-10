{-# OPTIONS --without-K #-}

-- WebGL Controls Audio Spectrum
--
-- Audio spectrum visualization: frequency bars, waterfall, circular spectrum.
-- Designed for real-time audio data from Web Audio API.

module Agdelte.WebGL.Controls.Audio.Spectrum where

open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Float using (Float; _*_; _+_; _-_; -_)
open import Data.String using (String)
open import Data.List using (List; []; _∷_; length)
open import Data.Bool using (Bool; true; false; if_then_else_)

open import Agdelte.WebGL.Types
open import Agdelte.WebGL.Builder.Geometry.Primitives
open import Agdelte.WebGL.Controls.Theme

------------------------------------------------------------------------
-- Helper postulates
------------------------------------------------------------------------

postulate
  natToFloat : ℕ → Float
  sinF : Float → Float
  cosF : Float → Float
  clamp01 : Float → Float
  _<F_ : Float → Float → Bool
  _>F_ : Float → Float → Bool

{-# COMPILE JS natToFloat = n => Number(n) #-}
{-# COMPILE JS sinF = x => Math.sin(x) #-}
{-# COMPILE JS cosF = x => Math.cos(x) #-}
{-# COMPILE JS clamp01 = x => Math.min(1, Math.max(0, x)) #-}
{-# COMPILE JS _<F_ = x => y => x < y #-}
{-# COMPILE JS _>F_ = x => y => x > y #-}

-- Helper: natural number less-than
ltNat : ℕ → ℕ → Bool
ltNat zero (suc _) = true
ltNat _ zero = false
ltNat (suc m) (suc n) = ltNat m n

------------------------------------------------------------------------
-- Spectrum configuration
------------------------------------------------------------------------

record SpectrumConfig : Set where
  constructor mkSpectrumConfig
  field
    barCount    : ℕ               -- Number of frequency bars
    width       : Float           -- Total width
    height      : Float           -- Maximum height
    depth       : Float           -- Bar depth
    spacing     : Float           -- Space between bars
    smoothing   : Float           -- Smoothing factor (0-1)

defaultSpectrumConfig : SpectrumConfig
defaultSpectrumConfig = mkSpectrumConfig
  32                              -- barCount
  1.0                             -- width
  0.5                             -- height
  0.02                            -- depth
  0.005                           -- spacing
  0.8                             -- smoothing

highResSpectrumConfig : SpectrumConfig
highResSpectrumConfig = mkSpectrumConfig
  64                              -- barCount
  1.0                             -- width
  0.5                             -- height
  0.015                           -- depth
  0.002                           -- spacing
  0.7                             -- smoothing

------------------------------------------------------------------------
-- Color mapping for magnitude
------------------------------------------------------------------------

MagnitudeColorMap : Set
MagnitudeColorMap = Float → GlColor

-- Default color maps
greenToRedMap : MagnitudeColorMap
greenToRedMap mag =
  let t = clamp01 mag
      r = t
      g = 1.0 - t
      b = 0.2
  in rgba r g b 1.0

rainbowMap : MagnitudeColorMap
rainbowMap mag =
  let t = clamp01 mag * 0.8  -- Limit to avoid wrapping
      r = 0.5 + 0.5 * sinF (t * 6.28 + 0.0)
      g = 0.5 + 0.5 * sinF (t * 6.28 + 2.09)
      b = 0.5 + 0.5 * sinF (t * 6.28 + 4.19)
  in rgba r g b 1.0

blueGlowMap : MagnitudeColorMap
blueGlowMap mag =
  let t = clamp01 mag
      r = t * 0.3
      g = t * 0.6
      b = 0.4 + t * 0.6
  in rgba r g b 1.0

fireMap : MagnitudeColorMap
fireMap mag =
  let t = clamp01 mag
      r = if t <F 0.5 then t * 2.0 else 1.0
      g = if t <F 0.5 then 0.0 else (t - 0.5) * 2.0
      b = 0.0
  in rgba r g b 1.0

------------------------------------------------------------------------
-- Frequency bars
------------------------------------------------------------------------

-- Vertical frequency bars
frequencyBars3D : ∀ {M Msg}
                → ControlTheme
                → SpectrumConfig
                → MagnitudeColorMap
                → (M → List Float)            -- Frequency magnitudes (0-1)
                → Transform
                → SceneNode M Msg
frequencyBars3D {M} {Msg} theme config colorMap getMagnitudes t =
  bindChildren buildBars t
  where
    barCount = SpectrumConfig.barCount config
    totalWidth = SpectrumConfig.width config
    maxHeight = SpectrumConfig.height config
    barDepth = SpectrumConfig.depth config
    spacing = SpectrumConfig.spacing config

    postulate recip : Float → Float
    {-# COMPILE JS recip = x => 1 / x #-}

    barWidth : Float
    barWidth = (totalWidth - spacing * natToFloat barCount) * recip (natToFloat barCount)

    buildBarList : Float → ℕ → List Float → List (SceneNode M Msg)
    buildBarList _ _ [] = []
    buildBarList startX idx (mag ∷ mags) =
      if ltNat idx barCount
        then (let x = startX + natToFloat idx * (barWidth + spacing)
                  -- Clamp magnitude
                  m = clamp01 mag
                  -- Bar height (minimum 0.01 to always show something)
                  height = maxHeight * m + 0.01
                  -- Position (centered on bottom)
                  y = height * 0.5
                  barT = mkTransform (vec3 x y 0.0) identityQuat (vec3 1.0 1.0 1.0)
                  -- Geometry and material
                  barGeom = roundedBox (vec3 barWidth height barDepth) (barWidth * 0.2) 4
                  barColor = colorMap m
                  barMat = phong barColor 48.0
              in (mesh barGeom barMat [] barT ∷ buildBarList startX (suc idx) mags))
        else []

    buildBars : M → List (SceneNode M Msg)
    buildBars m =
      let mags = getMagnitudes m
          startX = - (totalWidth * 0.5) + barWidth * 0.5
      in buildBarList startX 0 mags

-- Simple frequency bars
frequencyBars : ∀ {M Msg}
              → ControlTheme
              → (M → List Float)
              → Transform
              → SceneNode M Msg
frequencyBars theme = frequencyBars3D theme defaultSpectrumConfig greenToRedMap

------------------------------------------------------------------------
-- Circular spectrum
------------------------------------------------------------------------

record CircularSpectrumConfig : Set where
  constructor mkCircularSpectrumConfig
  field
    barCount     : ℕ
    innerRadius  : Float
    outerRadius  : Float          -- Maximum outer radius
    barDepth     : Float

defaultCircularConfig : CircularSpectrumConfig
defaultCircularConfig = mkCircularSpectrumConfig
  48                              -- barCount
  0.15                            -- innerRadius
  0.4                             -- outerRadius
  0.02                            -- barDepth

-- Circular frequency spectrum
circularSpectrum3D : ∀ {M Msg}
                   → ControlTheme
                   → CircularSpectrumConfig
                   → MagnitudeColorMap
                   → (M → List Float)
                   → Transform
                   → SceneNode M Msg
circularSpectrum3D {M} {Msg} theme config colorMap getMagnitudes t =
  bindChildren buildCircle t
  where
    barCount = CircularSpectrumConfig.barCount config
    innerR = CircularSpectrumConfig.innerRadius config
    outerR = CircularSpectrumConfig.outerRadius config
    barDepth = CircularSpectrumConfig.barDepth config
    pi = 3.14159
    twoPi = 2.0 * pi

    postulate recip : Float → Float
    {-# COMPILE JS recip = x => 1 / x #-}

    -- Create quaternion from angle (rotation around Z axis)
    quatFromAngle : Float → Quat
    quatFromAngle a =
      let halfA = a * 0.5
      in quat 0.0 0.0 (sinF halfA) (cosF halfA)

    buildBarList : Float → Float → ℕ → List Float → List (SceneNode M Msg)
    buildBarList _ _ _ [] = []
    buildBarList angle angleStep idx (mag ∷ mags) =
      if ltNat idx barCount
        then (let m = clamp01 mag
                  -- Bar length based on magnitude
                  barLen = innerR + (outerR - innerR) * m
                  -- Bar center position
                  midR = (innerR + barLen) * 0.5
                  x = midR * cosF angle
                  y = midR * sinF angle
                  -- Bar dimensions
                  barWidth = twoPi * innerR * recip (natToFloat barCount) * 0.8
                  barHeight = barLen - innerR + 0.01
                  barT = mkTransform (vec3 x y 0.0)
                           (quatFromAngle angle)
                           (vec3 1.0 1.0 1.0)
                  barGeom = roundedBox (vec3 barWidth barHeight barDepth) (barWidth * 0.2) 4
                  barColor = colorMap m
                  barMat = phong barColor 48.0
              in (mesh barGeom barMat [] barT
                  ∷ buildBarList (angle + angleStep) angleStep (suc idx) mags))
        else []

    buildCircle : M → List (SceneNode M Msg)
    buildCircle m =
      let mags = getMagnitudes m
          angleStep = twoPi * recip (natToFloat barCount)
      in buildBarList 0.0 angleStep 0 mags

-- Simple circular spectrum
circularSpectrum : ∀ {M Msg}
                 → ControlTheme
                 → (M → List Float)
                 → Transform
                 → SceneNode M Msg
circularSpectrum theme = circularSpectrum3D theme defaultCircularConfig rainbowMap

------------------------------------------------------------------------
-- Waterfall spectrum (history visualization)
------------------------------------------------------------------------

record WaterfallConfig : Set where
  constructor mkWaterfallConfig
  field
    barCount      : ℕ              -- Frequency bins
    historyDepth  : ℕ              -- Number of history rows
    width         : Float
    height        : Float
    depth         : Float          -- Z extent for history

defaultWaterfallConfig : WaterfallConfig
defaultWaterfallConfig = mkWaterfallConfig
  32                              -- barCount
  20                              -- historyDepth
  1.0                             -- width
  0.3                             -- height
  0.5                             -- depth

-- Waterfall spectrum (requires history in model)
waterfallSpectrum3D : ∀ {M Msg}
                    → ControlTheme
                    → WaterfallConfig
                    → MagnitudeColorMap
                    → (M → List (List Float))   -- History of magnitude rows
                    → Transform
                    → SceneNode M Msg
waterfallSpectrum3D {M} {Msg} theme config colorMap getHistory t =
  bindChildren buildWaterfall t
  where
    barCount = WaterfallConfig.barCount config
    historyDepth = WaterfallConfig.historyDepth config
    totalWidth = WaterfallConfig.width config
    maxHeight = WaterfallConfig.height config
    totalDepth = WaterfallConfig.depth config

    postulate recip : Float → Float
    {-# COMPILE JS recip = x => 1 / x #-}

    cellWidth : Float
    cellWidth = totalWidth * recip (natToFloat barCount)

    cellDepth : Float
    cellDepth = totalDepth * recip (natToFloat historyDepth)

    infixr 5 _++L_
    _++L_ : List (SceneNode M Msg) → List (SceneNode M Msg) → List (SceneNode M Msg)
    [] ++L ys = ys
    (x ∷ xs) ++L ys = x ∷ (xs ++L ys)

    buildRow : Float → Float → ℕ → List Float → List (SceneNode M Msg)
    buildRow _ _ _ [] = []
    buildRow startX z colIdx (mag ∷ mags) =
      if ltNat colIdx barCount
        then (let x = startX + natToFloat colIdx * cellWidth
                  m = clamp01 mag
                  height = maxHeight * m + 0.005
                  cellT = mkTransform (vec3 x (height * 0.5) z) identityQuat (vec3 1.0 1.0 1.0)
                  cellGeom = roundedBox (vec3 (cellWidth * 0.9) height (cellDepth * 0.9)) 0.002 4
                  cellColor = colorMap m
                  cellMat = phong cellColor 32.0
              in (mesh cellGeom cellMat [] cellT ∷ buildRow startX z (suc colIdx) mags))
        else []

    buildRows : Float → Float → ℕ → List (List Float) → List (SceneNode M Msg)
    buildRows _ _ _ [] = []
    buildRows startX startZ rowIdx (row ∷ rows) =
      if ltNat rowIdx historyDepth
        then (let z = startZ - natToFloat rowIdx * cellDepth
                  rowNodes = buildRow startX z 0 row
              in rowNodes ++L buildRows startX startZ (suc rowIdx) rows)
        else []

    buildWaterfall : M → List (SceneNode M Msg)
    buildWaterfall m =
      let history = getHistory m
          startX = - (totalWidth * 0.5) + cellWidth * 0.5
          startZ = totalDepth * 0.5 - cellDepth * 0.5
      in buildRows startX startZ 0 history

-- Simple waterfall
waterfallSpectrum : ∀ {M Msg}
                  → ControlTheme
                  → (M → List (List Float))
                  → Transform
                  → SceneNode M Msg
waterfallSpectrum theme = waterfallSpectrum3D theme defaultWaterfallConfig blueGlowMap

