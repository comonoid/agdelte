{-# OPTIONS --without-K #-}

-- WebGL Controls Text
--
-- Higher-level text components for UI controls.
-- Provides labels, value displays, and themed text helpers.

module Agdelte.WebGL.Controls.Text where

open import Data.List using (List; []; _∷_)
open import Data.Float using (Float)
open import Data.String using (String)
open import Agdelte.WebGL.Types
open import Agdelte.WebGL.Controls.Theme

------------------------------------------------------------------------
-- Static text helpers
------------------------------------------------------------------------

-- Label text (themed, static)
label : ∀ {M Msg} → ControlTheme → String → Transform → SceneNode M Msg
label theme str t = text3D str (labelStyle theme) [] t

-- Value display text (themed, static)
valueText : ∀ {M Msg} → ControlTheme → String → Transform → SceneNode M Msg
valueText theme str t = text3D str (valueStyle theme) [] t

-- Centered label at position
centeredLabel : ∀ {M Msg} → ControlTheme → String → Vec3 → SceneNode M Msg
centeredLabel theme str pos =
  label theme str (mkTransform pos identityQuat (vec3 1.0 1.0 1.0))

------------------------------------------------------------------------
-- Reactive text helpers
------------------------------------------------------------------------

-- Label that changes with model
dynamicLabel : ∀ {M Msg} → ControlTheme → (M → String) → Transform
             → SceneNode M Msg
dynamicLabel theme extract t = bindText3D extract (labelStyle theme) [] t

-- Value that changes with model
dynamicValue : ∀ {M Msg} → ControlTheme → (M → String) → Transform
             → SceneNode M Msg
dynamicValue theme extract t = bindText3D extract (valueStyle theme) [] t

------------------------------------------------------------------------
-- Custom-styled text
------------------------------------------------------------------------

-- Text with custom size (themed colors)
sizedLabel : ∀ {M Msg} → ControlTheme → Float → String → Transform
           → SceneNode M Msg
sizedLabel theme size str t =
  text3D str
    (mkTextStyle (builtin sans) size (ControlTheme.foregroundColor theme) center singleLine)
    [] t

-- Text with custom color
coloredText : ∀ {M Msg} → GlColor → Float → String → Transform
            → SceneNode M Msg
coloredText color size str t =
  text3D str
    (mkTextStyle (builtin sans) size color center singleLine)
    [] t

-- Monospace text (for code, numbers)
monoText : ∀ {M Msg} → ControlTheme → String → Transform → SceneNode M Msg
monoText theme str t =
  text3D str
    (mkTextStyle (builtin mono) (ControlTheme.labelSize theme) (ControlTheme.foregroundColor theme) left singleLine)
    [] t

------------------------------------------------------------------------
-- Text alignment variants
------------------------------------------------------------------------

-- Left-aligned label
leftLabel : ∀ {M Msg} → ControlTheme → String → Transform → SceneNode M Msg
leftLabel theme str t =
  text3D str
    (mkTextStyle (builtin sans) (ControlTheme.labelSize theme) (ControlTheme.foregroundColor theme) left singleLine)
    [] t

-- Right-aligned label
rightLabel : ∀ {M Msg} → ControlTheme → String → Transform → SceneNode M Msg
rightLabel theme str t =
  text3D str
    (mkTextStyle (builtin sans) (ControlTheme.labelSize theme) (ControlTheme.foregroundColor theme) right singleLine)
    [] t

------------------------------------------------------------------------
-- Clickable text
------------------------------------------------------------------------

-- Text that responds to clicks
clickableText : ∀ {M Msg} → ControlTheme → String → Msg → Transform
              → SceneNode M Msg
clickableText theme str msg t =
  text3D str (labelStyle theme) (onClick msg ∷ []) t

-- Dynamic clickable text
clickableDynamicText : ∀ {M Msg} → ControlTheme → (M → String) → Msg → Transform
                     → SceneNode M Msg
clickableDynamicText theme extract msg t =
  bindText3D extract (labelStyle theme) (onClick msg ∷ []) t

------------------------------------------------------------------------
-- Title and heading styles
------------------------------------------------------------------------

-- Large title text
titleText : ∀ {M Msg} → ControlTheme → String → Transform → SceneNode M Msg
titleText theme str t =
  text3D str
    (mkTextStyle (builtin sans) (ControlTheme.valueSize theme) (ControlTheme.primaryColor theme) center singleLine)
    [] t

-- Subtitle text
subtitleText : ∀ {M Msg} → ControlTheme → String → Transform → SceneNode M Msg
subtitleText theme str t =
  text3D str
    (mkTextStyle (builtin sans) (ControlTheme.labelSize theme) (ControlTheme.secondaryColor theme) center singleLine)
    [] t
