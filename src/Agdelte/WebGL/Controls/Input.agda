{-# OPTIONS --without-K #-}

-- WebGL Controls Input
--
-- Input fields for 3D UI: text input, number input, color picker.
-- Limited text input in 3D but useful for configuration panels.

module Agdelte.WebGL.Controls.Input where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Float using (Float; _*_; _+_; _-_; -_)
open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false; if_then_else_)

open import Agdelte.WebGL.Types
open import Agdelte.WebGL.Builder.Geometry.Primitives
open import Agdelte.WebGL.Controls.Theme
open import Agdelte.WebGL.Controls.Text
open import Agdelte.WebGL.Controls.Buttons

------------------------------------------------------------------------
-- Helper postulates
------------------------------------------------------------------------

postulate
  clamp : Float → Float → Float → Float
  showFloat : Float → String
  parseFloat : String → Float

{-# COMPILE JS clamp = (min) => (max) => (x) => Math.min(max, Math.max(min, x)) #-}
{-# COMPILE JS showFloat = x => x.toFixed(2) #-}
{-# COMPILE JS parseFloat = s => parseFloat(s) || 0 #-}

------------------------------------------------------------------------
-- Text input configuration
------------------------------------------------------------------------

record InputConfig : Set where
  constructor mkInputConfig
  field
    width     : Float
    height    : Float
    depth     : Float
    maxLength : ℕ

defaultInputConfig : InputConfig
defaultInputConfig = mkInputConfig 0.3 0.08 0.02 32

------------------------------------------------------------------------
-- Text input
------------------------------------------------------------------------

-- Text input field (displays text, clicks to focus for keyboard input)
textInput3D : ∀ {M Msg}
            → ControlTheme
            → InputConfig
            → (M → String)         -- Current value
            → (String → Msg)       -- onChange
            → Msg                  -- onFocus (for keyboard handling)
            → Transform
            → SceneNode M Msg
textInput3D theme config getValue onChange onFocus t =
  let w = InputConfig.width config
      h = InputConfig.height config
      d = InputConfig.depth config
      -- Background box
      bgGeom = roundedBox (vec3 w h d) (h * 0.2) 4
      bgMat = phong (ControlTheme.backgroundColor theme) 24.0
      -- Border frame
      frameGeom = roundedBox (vec3 (w + 0.01) (h + 0.01) (d * 0.5)) (h * 0.25) 4
      frameMat = phong (ControlTheme.foregroundColor theme) 32.0
      -- Text position
      textT = mkTransform (vec3 (- (w * 0.4)) 0.0 (d * 0.5 + 0.001)) identityQuat (vec3 1.0 1.0 1.0)
  in interactiveGroup
       (onClick onFocus ∷ [])
       t
       ( mesh frameGeom frameMat [] identityTransform
       ∷ mesh bgGeom bgMat []
           (mkTransform (vec3 0.0 0.0 0.01) identityQuat (vec3 1.0 1.0 1.0))
       ∷ dynamicValue theme getValue textT
       ∷ [])

-- Simple text input with defaults
textInput : ∀ {M Msg}
          → ControlTheme
          → (M → String)
          → (String → Msg)
          → Msg
          → Transform
          → SceneNode M Msg
textInput theme = textInput3D theme defaultInputConfig

------------------------------------------------------------------------
-- Number input (with +/- buttons)
------------------------------------------------------------------------

record NumberInputConfig : Set where
  constructor mkNumberInputConfig
  field
    width      : Float
    height     : Float
    depth      : Float
    minValue   : Float
    maxValue   : Float
    step       : Float

defaultNumberInputConfig : NumberInputConfig
defaultNumberInputConfig = mkNumberInputConfig 0.25 0.08 0.02 0.0 100.0 1.0

-- Number input with increment/decrement buttons
-- Takes separate Increment and Decrement messages
numberInput3D : ∀ {M Msg}
              → ControlTheme
              → NumberInputConfig
              → (M → Float)          -- Current value
              → Msg                  -- Decrement message
              → Msg                  -- Increment message
              → Transform
              → SceneNode M Msg
numberInput3D {M} {Msg} theme config getValue decMsg incMsg t =
  let w = NumberInputConfig.width config
      h = NumberInputConfig.height config
      d = NumberInputConfig.depth config
      btnW = h * 0.8
      -- Decrement button
      decT = mkTransform (vec3 (- (w * 0.5 + btnW * 0.6)) 0.0 0.0) identityQuat (vec3 1.0 1.0 1.0)
      decConfig = mkButtonConfig btnW h d (h * 0.2)
      -- Increment button
      incT = mkTransform (vec3 (w * 0.5 + btnW * 0.6) 0.0 0.0) identityQuat (vec3 1.0 1.0 1.0)
      incConfig = mkButtonConfig btnW h d (h * 0.2)
      -- Value display
      bgGeom = roundedBox (vec3 w h d) (h * 0.2) 4
      bgMat = phong (ControlTheme.backgroundColor theme) 24.0
      getValueStr = λ m → showFloat (getValue m)
      textT = mkTransform (vec3 0.0 0.0 (d * 0.5 + 0.001)) identityQuat (vec3 1.0 1.0 1.0)
  in group t
       ( mesh bgGeom bgMat [] identityTransform
       ∷ dynamicValue theme getValueStr textT
       ∷ button3D theme decConfig "−" decMsg decT
       ∷ button3D theme incConfig "+" incMsg incT
       ∷ [])

-- Simple number input
numberInput : ∀ {M Msg}
            → ControlTheme
            → (M → Float)
            → Msg                   -- Decrement
            → Msg                   -- Increment
            → Transform
            → SceneNode M Msg
numberInput theme = numberInput3D theme defaultNumberInputConfig

------------------------------------------------------------------------
-- Color picker
------------------------------------------------------------------------

data ColorPickerMode : Set where
  CubePicker   : ColorPickerMode   -- RGB cube
  WheelPicker  : ColorPickerMode   -- HSV wheel

record ColorPickerConfig : Set where
  constructor mkColorPickerConfig
  field
    size    : Float              -- Cube/sphere size
    depth   : Float
    mode    : ColorPickerMode

defaultColorPickerConfig : ColorPickerConfig
defaultColorPickerConfig = mkColorPickerConfig 0.2 0.02 CubePicker

-- Color picker (HSV wheel style)
colorPicker3D : ∀ {M Msg}
              → ControlTheme
              → ColorPickerConfig
              → (M → GlColor)        -- Current color
              → (GlColor → Msg)      -- onChange
              → Transform
              → SceneNode M Msg
colorPicker3D {M} {Msg} theme config getColor onChange t =
  let s = ColorPickerConfig.size config
      d = ColorPickerConfig.depth config
      -- Color wheel (simplified as a box grid showing color range)
      -- Full implementation would use custom shader for HSV wheel
      wheelR = s * 0.5
      -- Current color preview
      previewSize = s * 0.25
      previewT = mkTransform (vec3 (s * 0.4) 0.0 0.0) identityQuat (vec3 1.0 1.0 1.0)
      previewGeom = roundedBox (vec3 previewSize previewSize d) (previewSize * 0.15) 4
      getPreviewMat = λ m → phong (getColor m) 32.0
      -- Hue ring (simplified as colored segments)
      hueRingT = mkTransform (vec3 0.0 0.0 0.0) identityQuat (vec3 1.0 1.0 1.0)
  in group t
       ( buildHueRing wheelR d 0
       ∷ bindMaterial getPreviewMat previewGeom [] previewT
       ∷ [])
  where
    pi = 3.14159

    postulate
      sinF : Float → Float
      cosF : Float → Float

    {-# COMPILE JS sinF = x => Math.sin(x) #-}
    {-# COMPILE JS cosF = x => Math.cos(x) #-}

    natToFloat : ℕ → Float
    natToFloat zero = 0.0
    natToFloat (suc n) = 1.0 + natToFloat n

    -- HSV to RGB (simplified)
    hsvToColor : Float → GlColor
    hsvToColor hue =
      let r = 0.5 + 0.5 * cosF (hue * 2.0 * pi)
          g = 0.5 + 0.5 * cosF ((hue - 0.333) * 2.0 * pi)
          b = 0.5 + 0.5 * cosF ((hue - 0.666) * 2.0 * pi)
      in rgba r g b 1.0

    -- Build 12 colored segments for hue ring
    buildHueRing : Float → Float → ℕ → SceneNode M Msg
    buildHueRing r d n = group identityTransform (buildSegments r d 0 12)
      where
        segmentAngle = 2.0 * pi * (1.0 * (1.0 * (1.0 * (1.0 * (1.0 * (1.0 * (1.0 * (1.0 * (1.0 * (1.0 * (1.0 * (1.0 * 0.0833)))))))))))) -- 1/12

        buildSegments : Float → Float → ℕ → ℕ → List (SceneNode M Msg)
        buildSegments _ _ _ zero = []
        buildSegments radius depth idx (suc remaining) =
          let angle = natToFloat idx * segmentAngle * 12.0 * 2.0 * pi * (1.0 * (1.0 * (1.0 * 0.0833)))
              x = (radius * 0.75) * cosF angle
              y = (radius * 0.75) * sinF angle
              segT = mkTransform (vec3 x y 0.0) identityQuat (vec3 1.0 1.0 1.0)
              segGeom = sphere (radius * 0.12)
              hue = natToFloat idx * 0.0833
              segColor = hsvToColor hue
              segMat = phong segColor 32.0
              -- Click to select this hue
              selectMsg = onChange segColor
          in interactiveGroup
               (onClick selectMsg ∷ [])
               segT
               (mesh segGeom segMat [] identityTransform ∷ [])
             ∷ buildSegments radius depth (suc idx) remaining

-- Simple color picker
colorPicker : ∀ {M Msg}
            → ControlTheme
            → (M → GlColor)
            → (GlColor → Msg)
            → Transform
            → SceneNode M Msg
colorPicker theme = colorPicker3D theme defaultColorPickerConfig

------------------------------------------------------------------------
-- Labeled input variants
------------------------------------------------------------------------

labeledTextInput : ∀ {M Msg}
                 → ControlTheme
                 → String
                 → (M → String)
                 → (String → Msg)
                 → Msg
                 → Transform
                 → SceneNode M Msg
labeledTextInput theme lbl getValue onChange onFocus t =
  let labelT = mkTransform (vec3 (- 0.2) 0.0 0.0) identityQuat (vec3 1.0 1.0 1.0)
      inputT = mkTransform (vec3 0.1 0.0 0.0) identityQuat (vec3 1.0 1.0 1.0)
  in group t
       ( rightLabel theme lbl labelT
       ∷ textInput theme getValue onChange onFocus inputT
       ∷ [])

labeledNumberInput : ∀ {M Msg}
                   → ControlTheme
                   → String
                   → (M → Float)
                   → Msg                -- Decrement
                   → Msg                -- Increment
                   → Transform
                   → SceneNode M Msg
labeledNumberInput theme lbl getValue decMsg incMsg t =
  let labelT = mkTransform (vec3 (- 0.25) 0.0 0.0) identityQuat (vec3 1.0 1.0 1.0)
      inputT = mkTransform (vec3 0.1 0.0 0.0) identityQuat (vec3 1.0 1.0 1.0)
  in group t
       ( rightLabel theme lbl labelT
       ∷ numberInput theme getValue decMsg incMsg inputT
       ∷ [])

