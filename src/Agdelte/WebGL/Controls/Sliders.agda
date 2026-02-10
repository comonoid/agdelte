{-# OPTIONS --without-K #-}

-- WebGL Controls Sliders
--
-- 3D slider controls: linear sliders, dials/knobs, and range sliders.
-- Sliders allow continuous value selection through drag interaction.

module Agdelte.WebGL.Controls.Sliders where

open import Data.Nat using (ℕ)
open import Data.Float using (Float; _*_; _+_; _-_; -_)
open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false; if_then_else_)

open import Agdelte.WebGL.Types
open import Agdelte.WebGL.Builder.Geometry.Primitives
open import Agdelte.WebGL.Controls.Theme
open import Agdelte.WebGL.Controls.Text

------------------------------------------------------------------------
-- Helper postulates (Math functions)
------------------------------------------------------------------------

postulate
  clamp01 : Float → Float
  recip : Float → Float
  sinF : Float → Float
  cosF : Float → Float
  natToFloat : ℕ → Float
  floatToNat : Float → ℕ
  roundF : Float → Float

{-# COMPILE JS clamp01 = x => Math.max(0, Math.min(1, x)) #-}
{-# COMPILE JS recip = x => 1 / x #-}
{-# COMPILE JS sinF = x => Math.sin(x) #-}
{-# COMPILE JS cosF = x => Math.cos(x) #-}
{-# COMPILE JS natToFloat = n => Number(n) #-}
{-# COMPILE JS floatToNat = f => Math.round(f) | 0 #-}
{-# COMPILE JS roundF = x => Math.round(x) #-}

------------------------------------------------------------------------
-- Slider configuration
------------------------------------------------------------------------

record SliderConfig : Set where
  constructor mkSliderConfig
  field
    length       : Float      -- Track length
    trackRadius  : Float      -- Track thickness
    handleRadius : Float      -- Handle size
    showValue    : Bool       -- Display value text

-- Default horizontal slider
defaultSliderConfig : SliderConfig
defaultSliderConfig = mkSliderConfig 0.6 0.015 0.04 true

-- Thin slider
thinSliderConfig : SliderConfig
thinSliderConfig = mkSliderConfig 0.5 0.01 0.03 false

-- Large slider
largeSliderConfig : SliderConfig
largeSliderConfig = mkSliderConfig 0.8 0.02 0.05 true

------------------------------------------------------------------------
-- Slider value computation
------------------------------------------------------------------------

computeHSliderValue : Float → Vec3 → Vec3 → Float
computeHSliderValue len start current =
  let halfLen = len * 0.5
  in clamp01 ((vec3X current + halfLen) * recip len)

computeVSliderValue : Float → Vec3 → Vec3 → Float
computeVSliderValue len start current =
  let halfLen = len * 0.5
  in clamp01 ((vec3Y current + halfLen) * recip len)

------------------------------------------------------------------------
-- Linear slider (horizontal)
------------------------------------------------------------------------

-- Horizontal slider (value 0.0 to 1.0)
hslider3D : ∀ {M Msg}
          → ControlTheme
          → SliderConfig
          → (M → Float)         -- Current value (0-1)
          → (Float → Msg)       -- On change
          → Transform
          → SceneNode M Msg
hslider3D theme config getValue onChange t =
  let len = SliderConfig.length config
      tr = SliderConfig.trackRadius config
      hr = SliderConfig.handleRadius config
      -- Track geometry (cylinder lying on X axis)
      trackGeom = capsule tr len 12
      trackMat = phong (ControlTheme.disabledColor theme) 16.0
      -- Handle geometry (sphere)
      handleGeom = sphere hr
      handleMat = phong (ControlTheme.primaryColor theme) 64.0
      -- Handle position based on value
      getHandlePos = λ m →
        let v = getValue m
            x = (v - 0.5) * len
        in mkTransform (vec3 x 0.0 0.0) identityQuat (vec3 1.0 1.0 1.0)
      -- Track rotation (rotate to lie along X)
      trackRot = quat 0.0 0.0 0.707 0.707  -- 90° around Z
  in group t
       ( mesh trackGeom trackMat []
           (mkTransform (vec3 0.0 0.0 0.0) trackRot (vec3 1.0 1.0 1.0))
       ∷ bindTransform getHandlePos
           (interactiveGroup
             (onDrag (λ start current → onChange (computeHSliderValue len start current)) ∷ [])
             identityTransform
             (mesh handleGeom handleMat [] identityTransform ∷ []))
       ∷ [])

-- Simple horizontal slider with default config
hslider : ∀ {M Msg}
        → ControlTheme
        → (M → Float)
        → (Float → Msg)
        → Transform
        → SceneNode M Msg
hslider theme = hslider3D theme defaultSliderConfig

------------------------------------------------------------------------
-- Vertical slider
------------------------------------------------------------------------

vslider3D : ∀ {M Msg}
          → ControlTheme
          → SliderConfig
          → (M → Float)
          → (Float → Msg)
          → Transform
          → SceneNode M Msg
vslider3D theme config getValue onChange t =
  let len = SliderConfig.length config
      tr = SliderConfig.trackRadius config
      hr = SliderConfig.handleRadius config
      -- Track geometry (cylinder along Y axis - default orientation)
      trackGeom = capsule tr len 12
      trackMat = phong (ControlTheme.disabledColor theme) 16.0
      -- Handle
      handleGeom = sphere hr
      handleMat = phong (ControlTheme.primaryColor theme) 64.0
      -- Handle position based on value
      getHandlePos = λ m →
        let v = getValue m
            y = (v - 0.5) * len
        in mkTransform (vec3 0.0 y 0.0) identityQuat (vec3 1.0 1.0 1.0)
  in group t
       ( mesh trackGeom trackMat [] identityTransform
       ∷ bindTransform getHandlePos
           (interactiveGroup
             (onDrag (λ start current → onChange (computeVSliderValue len start current)) ∷ [])
             identityTransform
             (mesh handleGeom handleMat [] identityTransform ∷ []))
       ∷ [])

-- Simple vertical slider
vslider : ∀ {M Msg}
        → ControlTheme
        → (M → Float)
        → (Float → Msg)
        → Transform
        → SceneNode M Msg
vslider theme = vslider3D theme defaultSliderConfig

------------------------------------------------------------------------
-- Dial / Knob (rotary control)
------------------------------------------------------------------------

record DialConfig : Set where
  constructor mkDialConfig
  field
    radius     : Float        -- Dial radius
    thickness  : Float        -- Dial thickness (Z depth)
    minAngle   : Float        -- Start angle (radians)
    maxAngle   : Float        -- End angle (radians)

defaultDialConfig : DialConfig
defaultDialConfig = mkDialConfig 0.1 0.03 (-2.356) 2.356  -- -135° to +135°

computeDialValue : Float → Float → Vec3 → Vec3 → Float
computeDialValue minA maxA start current =
  let dx = vec3X current - vec3X start
      sensitivity = 0.01
      deltaAngle = dx * sensitivity
  in clamp01 (deltaAngle * recip (maxA - minA) + 0.5)

-- Rotary dial/knob
dial3D : ∀ {M Msg}
       → ControlTheme
       → DialConfig
       → (M → Float)          -- Value (0-1)
       → (Float → Msg)
       → Transform
       → SceneNode M Msg
dial3D theme config getValue onChange t =
  let r = DialConfig.radius config
      th = DialConfig.thickness config
      minA = DialConfig.minAngle config
      maxA = DialConfig.maxAngle config
      -- Dial body
      dialGeom = cylinder r th
      dialMat = phong (ControlTheme.backgroundColor theme) 32.0
      -- Indicator line (small cylinder on edge)
      indicatorGeom = cylinder 0.01 (r * 0.8)
      indicatorMat = phong (ControlTheme.primaryColor theme) 64.0
      -- Compute indicator rotation from value
      getIndicatorTransform = λ m →
        let v = getValue m
            angle = minA + v * (maxA - minA)
            -- Rotation around Z axis
            halfAngle = angle * 0.5
        in mkTransform (vec3 0.0 0.0 (th * 0.5 + 0.001))
             (quat 0.0 0.0 (sinF halfAngle) (cosF halfAngle))
             (vec3 1.0 1.0 1.0)
  in interactiveGroup
       (onScreenDrag (λ start current → onChange (computeDialValue minA maxA start current)) ∷ [])
       t
       ( mesh dialGeom dialMat [] identityTransform
       ∷ bindTransform getIndicatorTransform
           (mesh indicatorGeom indicatorMat [] identityTransform)
       ∷ [])

-- Simple dial with default config
dial : ∀ {M Msg}
     → ControlTheme
     → (M → Float)
     → (Float → Msg)
     → Transform
     → SceneNode M Msg
dial theme = dial3D theme defaultDialConfig

------------------------------------------------------------------------
-- Labeled slider (with value display)
------------------------------------------------------------------------

labeledSlider : ∀ {M Msg}
              → ControlTheme
              → String                -- Label
              → (M → Float)           -- Value
              → (Float → Msg)
              → (Float → String)      -- Value formatter
              → Transform
              → SceneNode M Msg
labeledSlider theme lbl getValue onChange format t =
  let sliderT = mkTransform (vec3 0.0 0.0 0.0) identityQuat (vec3 1.0 1.0 1.0)
      labelT = mkTransform (vec3 -0.35 0.0 0.0) identityQuat (vec3 1.0 1.0 1.0)
      valueT = mkTransform (vec3 0.4 0.0 0.0) identityQuat (vec3 1.0 1.0 1.0)
  in group t
       ( leftLabel theme lbl labelT
       ∷ hslider theme getValue onChange sliderT
       ∷ dynamicValue theme (λ m → format (getValue m)) valueT
       ∷ [])

------------------------------------------------------------------------
-- Integer slider helper
------------------------------------------------------------------------

-- Creates a slider that snaps to integer values
intSlider : ∀ {M Msg}
          → ControlTheme
          → ℕ                     -- Min value
          → ℕ                     -- Max value
          → (M → ℕ)               -- Current value
          → (ℕ → Msg)             -- On change
          → Transform
          → SceneNode M Msg
intSlider theme minVal maxVal getValue onChange t =
  let toFloat = λ n → natToFloat n
      fromFloat = λ f → floatToNat (roundF f)
      range = natToFloat maxVal - natToFloat minVal
      normalize = λ m → (toFloat (getValue m) - natToFloat minVal) * recip range
      denormalize = λ f → fromFloat (f * range + natToFloat minVal)
  in hslider theme normalize (λ f → onChange (denormalize f)) t
