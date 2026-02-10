{-# OPTIONS --without-K #-}

-- WebGL Controls Toggles
--
-- Toggle switches, checkboxes, and radio button groups.
-- Binary selection controls with visual state feedback.

module Agdelte.WebGL.Controls.Toggles where

open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Float using (Float; _*_; _+_; _-_; -_)
open import Data.String using (String)
open import Data.List using (List; []; _∷_; length)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Relation.Nullary using (yes; no)

open import Agdelte.WebGL.Types
open import Agdelte.WebGL.Builder.Geometry.Primitives
open import Agdelte.WebGL.Controls.Theme
open import Agdelte.WebGL.Controls.Text

------------------------------------------------------------------------
-- Helper postulates
------------------------------------------------------------------------

postulate
  natToFloat : ℕ → Float
  sinF : Float → Float
  cosF : Float → Float

{-# COMPILE JS natToFloat = n => Number(n) #-}
{-# COMPILE JS sinF = x => Math.sin(x) #-}
{-# COMPILE JS cosF = x => Math.cos(x) #-}

natEq : ℕ → ℕ → Bool
natEq m n with m ≟ n
... | yes _ = true
... | no _ = false

------------------------------------------------------------------------
-- Toggle switch (iOS/Android style)
------------------------------------------------------------------------

record ToggleConfig : Set where
  constructor mkToggleConfig
  field
    width      : Float      -- Total width
    height     : Float      -- Height
    depth      : Float      -- Z depth

defaultToggleConfig : ToggleConfig
defaultToggleConfig = mkToggleConfig 0.15 0.07 0.03

-- Toggle switch (lever style)
toggle3D : ∀ {M Msg}
         → ControlTheme
         → ToggleConfig
         → (M → Bool)           -- Is on?
         → Msg                  -- Toggle message
         → Transform
         → SceneNode M Msg
toggle3D theme config isOn toggleMsg t =
  let w = ToggleConfig.width config
      h = ToggleConfig.height config
      d = ToggleConfig.depth config
      handleR = h * 0.4
      -- Track (rounded box)
      trackGeom = roundedBox (vec3 w h d) (h * 0.5) 4
      -- Handle (sphere)
      handleGeom = sphere handleR
      handleMat = phong white 64.0
      -- Track material changes with state
      onColor = ControlTheme.primaryColor theme
      offColor = ControlTheme.disabledColor theme
      getTrackMat = λ m → if isOn m then phong onColor 32.0 else phong offColor 32.0
      -- Handle position (left when off, right when on)
      offset = (w - h) * 0.4
      getHandlePos = λ m →
        let x = if isOn m then offset else (- offset)
        in mkTransform (vec3 x 0.0 (d * 0.5 + handleR * 0.3)) identityQuat (vec3 1.0 1.0 1.0)
  in interactiveGroup
       (onClick toggleMsg ∷ transition (ms 150) easeOut ∷ [])
       t
       ( bindMaterial getTrackMat trackGeom [] identityTransform
       ∷ bindTransform getHandlePos
           (mesh handleGeom handleMat [] identityTransform)
       ∷ [])

-- Simple toggle with default config
toggle : ∀ {M Msg}
       → ControlTheme
       → (M → Bool)
       → Msg
       → Transform
       → SceneNode M Msg
toggle theme = toggle3D theme defaultToggleConfig

-- Toggle with label
labeledToggle : ∀ {M Msg}
              → ControlTheme
              → String
              → (M → Bool)
              → Msg
              → Transform
              → SceneNode M Msg
labeledToggle theme lbl isOn toggleMsg t =
  let toggleT = mkTransform (vec3 0.0 0.0 0.0) identityQuat (vec3 1.0 1.0 1.0)
      labelT = mkTransform (vec3 0.15 0.0 0.0) identityQuat (vec3 1.0 1.0 1.0)
  in group t
       ( toggle theme isOn toggleMsg toggleT
       ∷ leftLabel theme lbl labelT
       ∷ [])

------------------------------------------------------------------------
-- Checkbox
------------------------------------------------------------------------

record CheckboxConfig : Set where
  constructor mkCheckboxConfig
  field
    size  : Float
    depth : Float

defaultCheckboxConfig : CheckboxConfig
defaultCheckboxConfig = mkCheckboxConfig 0.08 0.02

-- Checkbox (box that fills when checked)
checkbox3D : ∀ {M Msg}
           → ControlTheme
           → CheckboxConfig
           → (M → Bool)
           → Msg
           → Transform
           → SceneNode M Msg
checkbox3D theme config isChecked toggleMsg t =
  let s = CheckboxConfig.size config
      d = CheckboxConfig.depth config
      innerS = s * 0.6
      -- Outer box (frame)
      frameGeom = roundedBox (vec3 s s d) (s * 0.15) 4
      frameMat = phong (ControlTheme.foregroundColor theme) 32.0
      -- Inner box (check indicator)
      checkGeom = roundedBox (vec3 innerS innerS (d * 1.2)) (innerS * 0.1) 4
      checkMat = phong (ControlTheme.primaryColor theme) 64.0
      -- Check visibility based on state
      getCheckScale = λ m →
        if isChecked m
          then mkTransform (vec3 0.0 0.0 0.0) identityQuat (vec3 1.0 1.0 1.0)
          else mkTransform (vec3 0.0 0.0 0.0) identityQuat (vec3 0.0 0.0 0.0)
  in interactiveGroup
       (onClick toggleMsg ∷ transition (ms 100) easeOut ∷ [])
       t
       ( mesh frameGeom frameMat [] identityTransform
       ∷ bindTransform getCheckScale
           (mesh checkGeom checkMat [] identityTransform)
       ∷ [])

-- Simple checkbox
checkbox : ∀ {M Msg}
         → ControlTheme
         → (M → Bool)
         → Msg
         → Transform
         → SceneNode M Msg
checkbox theme = checkbox3D theme defaultCheckboxConfig

-- Checkbox with label
labeledCheckbox : ∀ {M Msg}
                → ControlTheme
                → String
                → (M → Bool)
                → Msg
                → Transform
                → SceneNode M Msg
labeledCheckbox theme lbl isChecked toggleMsg t =
  let checkT = mkTransform (vec3 0.0 0.0 0.0) identityQuat (vec3 1.0 1.0 1.0)
      labelT = mkTransform (vec3 0.1 0.0 0.0) identityQuat (vec3 1.0 1.0 1.0)
  in group t
       ( checkbox theme isChecked toggleMsg checkT
       ∷ leftLabel theme lbl labelT
       ∷ [])

------------------------------------------------------------------------
-- Radio button
------------------------------------------------------------------------

record RadioConfig : Set where
  constructor mkRadioConfig
  field
    radius : Float
    depth  : Float

defaultRadioConfig : RadioConfig
defaultRadioConfig = mkRadioConfig 0.04 0.02

-- Single radio button
radio3D : ∀ {M Msg}
        → ControlTheme
        → RadioConfig
        → (M → Bool)            -- Is selected?
        → Msg                   -- Select message
        → Transform
        → SceneNode M Msg
radio3D theme config isSelected selectMsg t =
  let r = RadioConfig.radius config
      d = RadioConfig.depth config
      innerR = r * 0.5
      -- Outer ring
      ringGeom = torus r (r * 0.15) 24 8
      ringMat = phong (ControlTheme.foregroundColor theme) 32.0
      -- Inner dot (selection indicator)
      dotGeom = cylinder innerR d
      dotMat = phong (ControlTheme.primaryColor theme) 64.0
      -- Dot visibility
      getDotScale = λ m →
        if isSelected m
          then mkTransform (vec3 0.0 0.0 0.0) identityQuat (vec3 1.0 1.0 1.0)
          else mkTransform (vec3 0.0 0.0 0.0) identityQuat (vec3 0.0 0.0 0.0)
  in interactiveGroup
       (onClick selectMsg ∷ transition (ms 100) easeOut ∷ [])
       t
       ( mesh ringGeom ringMat [] identityTransform
       ∷ bindTransform getDotScale
           (mesh dotGeom dotMat [] identityTransform)
       ∷ [])

-- Radio with label
labeledRadio : ∀ {M Msg}
             → ControlTheme
             → String
             → (M → Bool)
             → Msg
             → Transform
             → SceneNode M Msg
labeledRadio theme lbl isSelected selectMsg t =
  let radioT = mkTransform (vec3 0.0 0.0 0.0) identityQuat (vec3 1.0 1.0 1.0)
      labelT = mkTransform (vec3 0.08 0.0 0.0) identityQuat (vec3 1.0 1.0 1.0)
  in group t
       ( radio3D theme defaultRadioConfig isSelected selectMsg radioT
       ∷ leftLabel theme lbl labelT
       ∷ [])

------------------------------------------------------------------------
-- Radio group (mutually exclusive options)
------------------------------------------------------------------------

-- Build radio options positioned vertically
radioGroupVertical : ∀ {M Msg}
                   → ControlTheme
                   → Float                    -- Spacing between items
                   → (M → ℕ)                  -- Selected index
                   → (ℕ → Msg)                -- Select handler
                   → List String              -- Labels
                   → Transform
                   → SceneNode M Msg
radioGroupVertical {M} {Msg} theme spacing getSelected selectHandler labels t =
  group t (buildRadios 0 labels)
  where
    buildRadios : ℕ → List String → List (SceneNode M Msg)
    buildRadios _ [] = []
    buildRadios idx (lbl ∷ rest) =
      let y = - (natToFloat idx * spacing)
          itemT = mkTransform (vec3 0.0 y 0.0) identityQuat (vec3 1.0 1.0 1.0)
          isSelected = λ m → natEq (getSelected m) idx
      in labeledRadio theme lbl isSelected (selectHandler idx) itemT
         ∷ buildRadios (suc idx) rest

-- Horizontal radio group
radioGroupHorizontal : ∀ {M Msg}
                     → ControlTheme
                     → Float
                     → (M → ℕ)
                     → (ℕ → Msg)
                     → List String
                     → Transform
                     → SceneNode M Msg
radioGroupHorizontal {M} {Msg} theme spacing getSelected selectHandler labels t =
  group t (buildRadios 0 labels)
  where
    buildRadios : ℕ → List String → List (SceneNode M Msg)
    buildRadios _ [] = []
    buildRadios idx (lbl ∷ rest) =
      let x = natToFloat idx * spacing
          itemT = mkTransform (vec3 x 0.0 0.0) identityQuat (vec3 1.0 1.0 1.0)
          isSelected = λ m → natEq (getSelected m) idx
      in labeledRadio theme lbl isSelected (selectHandler idx) itemT
         ∷ buildRadios (suc idx) rest

------------------------------------------------------------------------
-- Switch (alternative toggle style)
------------------------------------------------------------------------

-- Rocker switch style toggle
rockerSwitch3D : ∀ {M Msg}
               → ControlTheme
               → Float              -- Size
               → (M → Bool)
               → Msg
               → Transform
               → SceneNode M Msg
rockerSwitch3D theme size isOn toggleMsg t =
  let s = size
      d = s * 0.3
      -- Base
      baseGeom = roundedBox (vec3 s (s * 0.5) d) (s * 0.1) 4
      baseMat = phong (ControlTheme.backgroundColor theme) 32.0
      -- Rocker (tilts based on state)
      rockerGeom = roundedBox (vec3 (s * 0.9) (s * 0.4) (d * 0.8)) (s * 0.08) 4
      onMat = phong (ControlTheme.primaryColor theme) 48.0
      offMat = phong (ControlTheme.disabledColor theme) 48.0
      getRockerMat = λ m → if isOn m then onMat else offMat
      -- Rocker tilt
      tiltAngle = 0.2  -- radians
      getRockerTransform = λ m →
        let angle = if isOn m then tiltAngle else (- tiltAngle)
            halfAngle = angle * 0.5
        in mkTransform (vec3 0.0 0.0 (d * 0.3))
             (quat (sinF halfAngle) 0.0 0.0 (cosF halfAngle))
             (vec3 1.0 1.0 1.0)
  in interactiveGroup
       (onClick toggleMsg ∷ transition (ms 100) easeOut ∷ [])
       t
       ( mesh baseGeom baseMat [] identityTransform
       ∷ bindTransform getRockerTransform
           (bindMaterial getRockerMat rockerGeom [] identityTransform)
       ∷ [])
