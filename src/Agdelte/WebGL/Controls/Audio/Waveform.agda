{-# OPTIONS --without-K #-}

-- WebGL Controls Audio Waveform
--
-- Waveform visualization: oscilloscope, multi-channel, Lissajous figures.
-- Designed for real-time audio sample data.

module Agdelte.WebGL.Controls.Audio.Waveform where

open import Data.Nat using (ℕ; zero; suc)
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
  clamp : Float → Float → Float → Float
  absFloat : Float → Float
  _<F_ : Float → Float → Bool

{-# COMPILE JS natToFloat = n => Number(n) #-}
{-# COMPILE JS sinF = x => Math.sin(x) #-}
{-# COMPILE JS cosF = x => Math.cos(x) #-}
{-# COMPILE JS clamp = min => max => x => Math.min(max, Math.max(min, x)) #-}
{-# COMPILE JS absFloat = x => Math.abs(x) #-}
{-# COMPILE JS _<F_ = x => y => x < y #-}

-- Helper for natural number comparison
ltNat : ℕ → ℕ → Bool
ltNat zero (suc _) = true
ltNat _ zero = false
ltNat (suc m) (suc n) = ltNat m n

-- Product type at module level
open import Data.Product using (_×_; _,_; proj₁; proj₂)

------------------------------------------------------------------------
-- Waveform configuration
------------------------------------------------------------------------

record WaveformConfig : Set where
  constructor mkWaveformConfig
  field
    width       : Float           -- Display width
    height      : Float           -- Display height (amplitude range)
    depth       : Float           -- Z thickness
    lineWidth   : Float           -- Line/segment width
    sampleCount : ℕ               -- Maximum samples to display

defaultWaveformConfig : WaveformConfig
defaultWaveformConfig = mkWaveformConfig
  1.0                             -- width
  0.3                             -- height
  0.01                            -- depth
  0.005                           -- lineWidth
  256                             -- sampleCount

highResWaveformConfig : WaveformConfig
highResWaveformConfig = mkWaveformConfig
  1.0                             -- width
  0.3                             -- height
  0.01                            -- depth
  0.003                           -- lineWidth
  512                             -- sampleCount

------------------------------------------------------------------------
-- Oscilloscope
------------------------------------------------------------------------

-- Classic oscilloscope display
oscilloscope3D : ∀ {M Msg}
               → ControlTheme
               → WaveformConfig
               → GlColor
               → (M → List Float)          -- Audio samples (-1 to 1)
               → Transform
               → SceneNode M Msg
oscilloscope3D {M} {Msg} theme config color getSamples t =
  group t
    ( background
    ∷ bindChildren buildWaveform identityTransform
    ∷ [])
  where
    w = WaveformConfig.width config
    h = WaveformConfig.height config
    d = WaveformConfig.depth config
    lineW = WaveformConfig.lineWidth config
    maxSamples = WaveformConfig.sampleCount config

    postulate recip : Float → Float
    {-# COMPILE JS recip = x => 1 / x #-}

    -- Background panel
    background : SceneNode M Msg
    background =
      let bgGeom = roundedBox (vec3 w h (d * 0.5)) 0.01 4
          bgMat = phong (rgba 0.05 0.05 0.1 0.9) 16.0
      in mesh bgGeom bgMat [] identityTransform

    buildSegments : Float → Float → ℕ → List Float → List (SceneNode M Msg)
    buildSegments _ _ _ [] = []
    buildSegments startX stepX idx (sample ∷ samples) =
      if ltNat idx maxSamples
        then (let x = startX + natToFloat idx * stepX
                  -- Clamp sample to -1..1 range
                  s = clamp (- 1.0) 1.0 sample
                  -- Map to Y position
                  y = s * (h * 0.5)
                  -- Create segment
                  segT = mkTransform (vec3 x y (d * 0.5)) identityQuat (vec3 1.0 1.0 1.0)
                  segGeom = sphere lineW
                  segMat = phong color 64.0
              in (mesh segGeom segMat [] segT
                  ∷ buildSegments startX stepX (suc idx) samples))
        else []

    buildWaveform : M → List (SceneNode M Msg)
    buildWaveform m =
      let samples = getSamples m
          n = length samples
          effectiveN = if ltNat n maxSamples then n else maxSamples
          stepX = w * recip (natToFloat effectiveN)
          startX = - (w * 0.5) + stepX * 0.5
      in buildSegments startX stepX 0 samples

-- Simple oscilloscope
oscilloscope : ∀ {M Msg}
             → ControlTheme
             → GlColor
             → (M → List Float)
             → Transform
             → SceneNode M Msg
oscilloscope theme = oscilloscope3D theme defaultWaveformConfig

------------------------------------------------------------------------
-- Multi-channel waveform
------------------------------------------------------------------------

record MultiChannelConfig : Set where
  constructor mkMultiChannelConfig
  field
    width         : Float
    channelHeight : Float
    channelSpacing : Float
    depth         : Float
    lineWidth     : Float
    sampleCount   : ℕ

defaultMultiChannelConfig : MultiChannelConfig
defaultMultiChannelConfig = mkMultiChannelConfig
  1.0                             -- width
  0.15                            -- channelHeight
  0.05                            -- channelSpacing
  0.01                            -- depth
  0.004                           -- lineWidth
  256                             -- sampleCount

-- Multi-channel waveform display
multiChannelWaveform3D : ∀ {M Msg}
                       → ControlTheme
                       → MultiChannelConfig
                       → List GlColor                   -- Channel colors
                       → (M → List (List Float))     -- Channels of samples
                       → Transform
                       → SceneNode M Msg
multiChannelWaveform3D {M} {Msg} theme config colors getChannels t =
  bindChildren buildChannels t
  where
    w = MultiChannelConfig.width config
    chH = MultiChannelConfig.channelHeight config
    chSpacing = MultiChannelConfig.channelSpacing config
    d = MultiChannelConfig.depth config
    lineW = MultiChannelConfig.lineWidth config
    maxSamples = MultiChannelConfig.sampleCount config

    postulate recip : Float → Float
    {-# COMPILE JS recip = x => 1 / x #-}

    getColorAt : List GlColor → ℕ → GlColor
    getColorAt [] _ = rgba 0.0 1.0 0.0 1.0  -- green fallback
    getColorAt (c ∷ _) zero = c
    getColorAt (_ ∷ cs) (suc n) = getColorAt cs n

    buildWaveSegments : Float → Float → Float → Float → GlColor → ℕ → List Float → List (SceneNode M Msg)
    buildWaveSegments _ _ _ _ _ _ [] = []
    buildWaveSegments startX stepX h lw color idx (sample ∷ samples) =
      if ltNat idx maxSamples
        then (let x = startX + natToFloat idx * stepX
                  s = clamp (- 1.0) 1.0 sample
                  y = s * (h * 0.45)
                  segT = mkTransform (vec3 x y (d * 0.6)) identityQuat (vec3 1.0 1.0 1.0)
                  segGeom = sphere lw
                  segMat = phong color 64.0
              in (mesh segGeom segMat [] segT
                  ∷ buildWaveSegments startX stepX h lw color (suc idx) samples))
        else []

    buildWave : Float → Float → Float → GlColor → ℕ → List Float → List (SceneNode M Msg)
    buildWave ww hh lw color maxS samples =
      let n = length samples
          effectiveN = if ltNat n maxS then n else maxS
          stepX = ww * recip (natToFloat effectiveN)
          startX = - (ww * 0.5) + stepX * 0.5
      in buildWaveSegments startX stepX hh lw color 0 samples

    buildChannelList : Float → ℕ → List (List Float) → List (SceneNode M Msg)
    buildChannelList _ _ [] = []
    buildChannelList startY idx (ch ∷ chs) =
      let y = startY - natToFloat idx * (chH + chSpacing)
          color = getColorAt colors idx
          channelT = mkTransform (vec3 0.0 y 0.0) identityQuat (vec3 1.0 1.0 1.0)
          -- Background for this channel
          bgGeom = roundedBox (vec3 w chH (d * 0.5)) 0.005 4
          bgMat = phong (rgba 0.05 0.05 0.1 0.8) 16.0
          bgNode = mesh bgGeom bgMat [] identityTransform
          -- Waveform samples
          waveNodes = buildWave w chH lineW color maxSamples ch
      in group channelT (bgNode ∷ waveNodes)
         ∷ buildChannelList startY (suc idx) chs

    buildChannels : M → List (SceneNode M Msg)
    buildChannels m =
      let channels = getChannels m
          n = length channels
          totalH = natToFloat n * (chH + chSpacing) - chSpacing
          startY = totalH * 0.5 - chH * 0.5
      in buildChannelList startY 0 channels

-- Simple multi-channel
multiChannelWaveform : ∀ {M Msg}
                     → ControlTheme
                     → List GlColor
                     → (M → List (List Float))
                     → Transform
                     → SceneNode M Msg
multiChannelWaveform theme = multiChannelWaveform3D theme defaultMultiChannelConfig

------------------------------------------------------------------------
-- Lissajous figure
------------------------------------------------------------------------

record LissajousConfig : Set where
  constructor mkLissajousConfig
  field
    size        : Float           -- Display size
    depth       : Float           -- Z thickness
    lineWidth   : Float           -- Line width
    trailLength : ℕ               -- Number of trail points

defaultLissajousConfig : LissajousConfig
defaultLissajousConfig = mkLissajousConfig
  0.4                             -- size
  0.02                            -- depth
  0.005                           -- lineWidth
  256                             -- trailLength

-- Lissajous figure (X-Y mode oscilloscope)
lissajous3D : ∀ {M Msg}
            → ControlTheme
            → LissajousConfig
            → GlColor
            → (M → List Float)              -- X channel
            → (M → List Float)              -- Y channel
            → Transform
            → SceneNode M Msg
lissajous3D {M} {Msg} theme config color getX getY t =
  group t
    ( background
    ∷ bindChildren buildFigure identityTransform
    ∷ [])
  where
    sz = LissajousConfig.size config
    d = LissajousConfig.depth config
    lw = LissajousConfig.lineWidth config
    trailLen = LissajousConfig.trailLength config

    postulate recip : Float → Float
    {-# COMPILE JS recip = x => 1 / x #-}

    -- Background circle
    background : SceneNode M Msg
    background =
      let bgGeom = cylinder (sz * 0.55) (d * 0.5)
          bgMat = phong (rgba 0.05 0.05 0.1 0.9) 16.0
      in mesh bgGeom bgMat [] identityTransform

    -- Zip two lists
    zipLists : List Float → List Float → List (Float × Float)
    zipLists [] _ = []
    zipLists _ [] = []
    zipLists (xx ∷ xs) (yy ∷ ys) = (xx , yy) ∷ zipLists xs ys

    buildPoints : ℕ → List (Float × Float) → List (SceneNode M Msg)
    buildPoints _ [] = []
    buildPoints idx ((xVal , yVal) ∷ points) =
      if ltNat idx trailLen
        then (let -- Clamp to -1..1
                  x = clamp (- 1.0) 1.0 xVal * (sz * 0.5)
                  y = clamp (- 1.0) 1.0 yVal * (sz * 0.5)
                  -- Fade based on position in trail
                  fade = 1.0 - natToFloat idx * recip (natToFloat trailLen)
                  ptT = mkTransform (vec3 x y (d * 0.5)) identityQuat (vec3 1.0 1.0 1.0)
                  ptGeom = sphere (lw * fade + 0.001)
                  ptMat = phong color 64.0
              in (mesh ptGeom ptMat [] ptT
                  ∷ buildPoints (suc idx) points))
        else []

    buildFigure : M → List (SceneNode M Msg)
    buildFigure m =
      let xSamples = getX m
          ySamples = getY m
          points = zipLists xSamples ySamples
      in buildPoints 0 points

-- Simple Lissajous
lissajous : ∀ {M Msg}
          → ControlTheme
          → GlColor
          → (M → List Float)
          → (M → List Float)
          → Transform
          → SceneNode M Msg
lissajous theme = lissajous3D theme defaultLissajousConfig

------------------------------------------------------------------------
-- VU Meter
------------------------------------------------------------------------

record VUMeterConfig : Set where
  constructor mkVUMeterConfig
  field
    width   : Float
    height  : Float
    depth   : Float
    segments : ℕ

defaultVUMeterConfig : VUMeterConfig
defaultVUMeterConfig = mkVUMeterConfig
  0.3                             -- width
  0.05                            -- height
  0.02                            -- depth
  20                              -- segments

-- VU meter (level indicator)
vuMeter3D : ∀ {M Msg}
          → ControlTheme
          → VUMeterConfig
          → (M → Float)                   -- Level (0-1)
          → Transform
          → SceneNode M Msg
vuMeter3D {M} {Msg} theme config getLevel t =
  group t
    ( background
    ∷ bindChildren buildMeter identityTransform
    ∷ [])
  where
    w = VUMeterConfig.width config
    h = VUMeterConfig.height config
    d = VUMeterConfig.depth config
    segs = VUMeterConfig.segments config

    postulate recip : Float → Float
    postulate floor : Float → ℕ
    {-# COMPILE JS recip = x => 1 / x #-}
    {-# COMPILE JS floor = x => Math.floor(x) #-}

    background : SceneNode M Msg
    background =
      let bgGeom = roundedBox (vec3 (w + 0.01) (h + 0.01) (d * 0.5)) 0.005 4
          bgMat = phong (rgba 0.1 0.1 0.1 1.0) 16.0
      in mesh bgGeom bgMat [] identityTransform

    -- Use remaining count for termination proof
    buildSegmentsRec : Float → Float → ℕ → ℕ → ℕ → List (SceneNode M Msg)
    buildSegmentsRec _ _ _ _ zero = []
    buildSegmentsRec startX segW litSegs idx (suc remaining) =
      let x = startX + natToFloat idx * segW
          isLit = ltNat idx litSegs
          -- Color based on position (green -> yellow -> red)
          ratio = natToFloat idx * recip (natToFloat segs)
          segColor = if ratio <F 0.6
            then rgba 0.2 0.8 0.2 1.0      -- green
            else if ratio <F 0.85
              then rgba 0.9 0.8 0.1 1.0    -- yellow
              else rgba 0.9 0.2 0.1 1.0    -- red
          dimColor = rgba 0.15 0.15 0.15 1.0
          color = if isLit then segColor else dimColor
          segT = mkTransform (vec3 x 0.0 (d * 0.5)) identityQuat (vec3 1.0 1.0 1.0)
          segGeom = roundedBox (vec3 (segW * 0.85) (h * 0.8) d) 0.002 4
          segMat = phong color 48.0
      in mesh segGeom segMat [] segT
         ∷ buildSegmentsRec startX segW litSegs (suc idx) remaining

    buildMeter : M → List (SceneNode M Msg)
    buildMeter m =
      let level = clamp 0.0 1.0 (getLevel m)
          segW = w * recip (natToFloat segs)
          startX = - (w * 0.5) + segW * 0.5
          litSegs = floor (level * natToFloat segs)
      in buildSegmentsRec startX segW litSegs 0 segs

-- Simple VU meter
vuMeter : ∀ {M Msg}
        → ControlTheme
        → (M → Float)
        → Transform
        → SceneNode M Msg
vuMeter theme = vuMeter3D theme defaultVUMeterConfig

