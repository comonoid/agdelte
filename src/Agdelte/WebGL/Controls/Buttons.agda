{-# OPTIONS --without-K #-}

-- WebGL Controls Buttons
--
-- 3D button components with hover/active states and click handling.
-- Buttons use roundedBox geometry with text labels.

module Agdelte.WebGL.Controls.Buttons where

open import Data.Nat using (ℕ)
open import Data.Float using (Float; _*_; _+_; -_)
open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false; if_then_else_)

open import Agdelte.WebGL.Types
open import Agdelte.WebGL.Builder.Geometry.Primitives
open import Agdelte.WebGL.Controls.Theme
open import Agdelte.WebGL.Controls.State
open import Agdelte.WebGL.Controls.Text

------------------------------------------------------------------------
-- Button configuration
------------------------------------------------------------------------

record ButtonConfig : Set where
  constructor mkButtonConfig
  field
    width      : Float      -- Button width
    height     : Float      -- Button height
    depth      : Float      -- Button thickness (Z depth)
    radius     : Float      -- Corner radius

-- Default button size (2.5x larger for better visibility)
defaultButtonConfig : ButtonConfig
defaultButtonConfig = mkButtonConfig 1.0 0.3 0.1 0.05

-- Small button
smallButtonConfig : ButtonConfig
smallButtonConfig = mkButtonConfig 0.6 0.2 0.08 0.04

-- Large button
largeButtonConfig : ButtonConfig
largeButtonConfig = mkButtonConfig 1.5 0.4 0.12 0.06

------------------------------------------------------------------------
-- Simple buttons (stateless - hover handled by runtime animation)
------------------------------------------------------------------------

-- Basic 3D button
-- Uses interactiveGroup so both box and text respond to hover/click
button3D : ∀ {M Msg}
         → ControlTheme
         → ButtonConfig
         → String          -- Label
         → Msg             -- Click message
         → Transform
         → SceneNode M Msg
button3D theme config lbl msg t =
  let w = ButtonConfig.width config
      h = ButtonConfig.height config
      d = ButtonConfig.depth config
      r = ButtonConfig.radius config
      dims = vec3 w h d
      btnGeom = roundedBox dims r 4
      btnMat = ControlTheme.surfaceMaterial theme
      -- Position text slightly in front of button
      textOffset = vec3 0.0 0.0 (d * 0.5 + 0.001)
      textTransform = mkTransform textOffset identityQuat (vec3 1.0 1.0 1.0)
  in interactiveGroup
       (onClick msg ∷ transition (ms 150) easeOut ∷ [])
       t
       ( mesh btnGeom btnMat [] identityTransform
       ∷ label theme lbl textTransform
       ∷ [])

-- Button with default config (alias for button3D with defaultButtonConfig)
defaultButton3D : ∀ {M Msg}
                → ControlTheme
                → String
                → Msg
                → Transform
                → SceneNode M Msg
defaultButton3D theme = button3D theme defaultButtonConfig

-- Small button
smallButton3D : ∀ {M Msg}
              → ControlTheme
              → String
              → Msg
              → Transform
              → SceneNode M Msg
smallButton3D theme = button3D theme smallButtonConfig

-- Large button
largeButton3D : ∀ {M Msg}
              → ControlTheme
              → String
              → Msg
              → Transform
              → SceneNode M Msg
largeButton3D theme = button3D theme largeButtonConfig

------------------------------------------------------------------------
-- Icon button (no text, just an icon/symbol)
------------------------------------------------------------------------

-- Icon button using texture
iconButton : ∀ {M Msg}
           → ControlTheme
           → TextureHandle    -- Icon texture
           → Float            -- Size (width = height)
           → Msg
           → Transform
           → SceneNode M Msg
iconButton theme tex size msg t =
  let d = size * 0.25
      dims = vec3 size size d
      btnGeom = roundedBox dims (size * 0.1) 4
      btnMat = ControlTheme.surfaceMaterial theme
      iconOffset = vec3 0.0 0.0 (d * 0.5 + 0.001)
      iconTransform = mkTransform iconOffset identityQuat (vec3 1.0 1.0 1.0)
      iconSize = vec2 (size * 0.7) (size * 0.7)
  in interactiveGroup
       (onClick msg ∷ transition (ms 150) easeOut ∷ [])
       t
       ( mesh btnGeom btnMat [] identityTransform
       ∷ icon tex iconSize [] iconTransform
       ∷ [])

------------------------------------------------------------------------
-- Floating action button (circular)
------------------------------------------------------------------------

fab : ∀ {M Msg}
    → ControlTheme
    → TextureHandle    -- Icon texture
    → Float            -- Radius
    → Msg
    → Transform
    → SceneNode M Msg
fab theme tex radius msg t =
  let btnGeom = sphere radius
      btnMat = phong (ControlTheme.primaryColor theme) 64.0
      iconOffset = vec3 0.0 0.0 (radius + 0.001)
      iconTransform = mkTransform iconOffset identityQuat (vec3 1.0 1.0 1.0)
      iconSize = vec2 (radius * 1.2) (radius * 1.2)
  in interactiveGroup
       (onClick msg ∷ transition (ms 150) easeOut ∷ [])
       t
       ( mesh btnGeom btnMat [] identityTransform
       ∷ icon tex iconSize [] iconTransform
       ∷ [])

------------------------------------------------------------------------
-- Push button (physically presses down on click)
------------------------------------------------------------------------

-- Button that visually "pushes" when clicked
-- Requires tracking pressed state in model
pushButton : ∀ {M Msg}
           → ControlTheme
           → ButtonConfig
           → String
           → (M → Bool)      -- Is pressed?
           → Msg             -- On press (mousedown)
           → Msg             -- On release (mouseup/leave)
           → Transform
           → SceneNode M Msg
pushButton theme config lbl isPressed pressMsg releaseMsg t =
  let w = ButtonConfig.width config
      h = ButtonConfig.height config
      d = ButtonConfig.depth config
      r = ButtonConfig.radius config
      dims = vec3 w h d
      btnGeom = roundedBox dims r 4
      btnMat = ControlTheme.surfaceMaterial theme
      -- Transform based on pressed state
      pressedOffset = d * 0.3
      pressedTransform = mkTransform (vec3 0.0 0.0 (- pressedOffset)) identityQuat (vec3 1.0 1.0 1.0)
      getTransform = λ m → if isPressed m then pressedTransform else identityTransform
      textOffset = vec3 0.0 0.0 (d * 0.5 + 0.001)
      textTransform = mkTransform textOffset identityQuat (vec3 1.0 1.0 1.0)
  in bindTransform getTransform
       (interactiveGroup
         (onHover releaseMsg ∷ onClick pressMsg ∷ transition (ms 80) easeOut ∷ [])
         t
         ( mesh btnGeom btnMat [] identityTransform
         ∷ label theme lbl textTransform
         ∷ []))

------------------------------------------------------------------------
-- Toggle button (stays pressed until toggled off)
------------------------------------------------------------------------

toggleButton : ∀ {M Msg}
             → ControlTheme
             → ButtonConfig
             → String
             → (M → Bool)      -- Is toggled on?
             → Msg             -- Toggle message
             → Transform
             → SceneNode M Msg
toggleButton theme config lbl isOn toggleMsg t =
  let w = ButtonConfig.width config
      h = ButtonConfig.height config
      d = ButtonConfig.depth config
      r = ButtonConfig.radius config
      dims = vec3 w h d
      btnGeom = roundedBox dims r 4
      -- Material changes based on toggle state
      onMaterial = phong (ControlTheme.primaryColor theme) 32.0
      offMaterial = ControlTheme.surfaceMaterial theme
      getMaterial = λ m → if isOn m then onMaterial else offMaterial
      textOffset = vec3 0.0 0.0 (d * 0.5 + 0.001)
      textTransform = mkTransform textOffset identityQuat (vec3 1.0 1.0 1.0)
  in interactiveGroup
       (onClick toggleMsg ∷ transition (ms 150) easeOut ∷ [])
       t
       ( bindMaterial getMaterial btnGeom [] identityTransform
       ∷ label theme lbl textTransform
       ∷ [])

------------------------------------------------------------------------
-- Disabled button (no interaction)
------------------------------------------------------------------------

disabledButton : ∀ {M Msg}
               → ControlTheme
               → ButtonConfig
               → String
               → Transform
               → SceneNode M Msg
disabledButton theme config lbl t =
  let w = ButtonConfig.width config
      h = ButtonConfig.height config
      d = ButtonConfig.depth config
      r = ButtonConfig.radius config
      dims = vec3 w h d
      btnGeom = roundedBox dims r 4
      btnMat = disabledMaterial theme
      textOffset = vec3 0.0 0.0 (d * 0.5 + 0.001)
      textStyle = mkTextStyle (builtin sans) (ControlTheme.labelSize theme)
                    (ControlTheme.disabledColor theme) center singleLine
  in group t
       ( mesh btnGeom btnMat [] identityTransform
       ∷ text3D lbl textStyle [] (mkTransform textOffset identityQuat (vec3 1.0 1.0 1.0))
       ∷ [])
