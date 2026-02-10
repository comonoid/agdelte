{-# OPTIONS --without-K #-}

-- WebGL Controls Theme
--
-- Defines color schemes and styling for 3D UI controls.
-- Themes provide consistent visual appearance across all controls.

module Agdelte.WebGL.Controls.Theme where

open import Data.Float using (Float)
open import Agdelte.WebGL.Types

------------------------------------------------------------------------
-- Theme definition
------------------------------------------------------------------------

record ControlTheme : Set where
  constructor mkTheme
  field
    -- Primary colors
    primaryColor     : GlColor    -- Main accent color
    secondaryColor   : GlColor    -- Secondary accent
    backgroundColor  : GlColor    -- Control backgrounds
    foregroundColor  : GlColor    -- Text and icons

    -- State colors
    hoverColor       : GlColor    -- Hover highlight
    activeColor      : GlColor    -- Pressed/active state
    disabledColor    : GlColor    -- Disabled controls

    -- Materials for 3D surfaces
    surfaceMaterial  : Material   -- Default control surface
    frameMaterial    : Material   -- Borders and frames

    -- Dimensions (in world units)
    cornerRadius     : Float      -- Rounded corners
    borderWidth      : Float      -- Frame thickness
    padding          : Float      -- Internal spacing

    -- Text styling
    labelSize        : Float      -- Label text size
    valueSize        : Float      -- Value display size

------------------------------------------------------------------------
-- Default theme (light)
------------------------------------------------------------------------

-- Colors
defaultPrimary : GlColor
defaultPrimary = rgb 0.2 0.5 0.9      -- Blue

defaultSecondary : GlColor
defaultSecondary = rgb 0.4 0.7 0.3    -- Green

defaultBackground : GlColor
defaultBackground = rgb 0.95 0.95 0.95  -- Light gray

defaultForeground : GlColor
defaultForeground = rgb 0.15 0.15 0.15  -- Dark gray (text)

defaultHover : GlColor
defaultHover = rgb 0.3 0.6 1.0        -- Lighter blue

defaultActive : GlColor
defaultActive = rgb 0.1 0.4 0.8       -- Darker blue

defaultDisabled : GlColor
defaultDisabled = rgb 0.6 0.6 0.6     -- Gray

defaultTheme : ControlTheme
defaultTheme = mkTheme
  defaultPrimary
  defaultSecondary
  defaultBackground
  defaultForeground
  defaultHover
  defaultActive
  defaultDisabled
  (phong defaultBackground 32.0)  -- surfaceMaterial
  (phong defaultForeground 16.0)  -- frameMaterial
  0.05                            -- cornerRadius
  0.01                            -- borderWidth
  0.02                            -- padding
  0.08                            -- labelSize
  0.12                            -- valueSize

------------------------------------------------------------------------
-- Dark theme
------------------------------------------------------------------------

darkPrimary : GlColor
darkPrimary = rgb 0.3 0.7 1.0         -- Bright blue

darkSecondary : GlColor
darkSecondary = rgb 0.5 0.9 0.4       -- Bright green

darkBackground : GlColor
darkBackground = rgb 0.15 0.15 0.18   -- Dark gray

darkForeground : GlColor
darkForeground = rgb 0.9 0.9 0.9      -- Light (text)

darkHover : GlColor
darkHover = rgb 0.4 0.8 1.0           -- Lighter blue

darkActive : GlColor
darkActive = rgb 0.2 0.6 0.9          -- Medium blue

darkDisabled : GlColor
darkDisabled = rgb 0.4 0.4 0.4        -- Dark gray

darkTheme : ControlTheme
darkTheme = mkTheme
  darkPrimary
  darkSecondary
  darkBackground
  darkForeground
  darkHover
  darkActive
  darkDisabled
  (phong darkBackground 32.0)   -- surfaceMaterial
  (phong darkPrimary 16.0)      -- frameMaterial
  0.05                          -- cornerRadius
  0.01                          -- borderWidth
  0.02                          -- padding
  0.08                          -- labelSize
  0.12                          -- valueSize

------------------------------------------------------------------------
-- Theme utilities
------------------------------------------------------------------------

-- Get label TextStyle from theme
labelStyle : ControlTheme → TextStyle
labelStyle theme = mkTextStyle
  (builtin sans)
  (ControlTheme.labelSize theme)
  (ControlTheme.foregroundColor theme)
  center
  singleLine

-- Get value display TextStyle from theme
valueStyle : ControlTheme → TextStyle
valueStyle theme = mkTextStyle
  (builtin mono)
  (ControlTheme.valueSize theme)
  (ControlTheme.primaryColor theme)
  center
  singleLine

-- Material for control in normal state
normalMaterial : ControlTheme → Material
normalMaterial = ControlTheme.surfaceMaterial

-- Material for hovered control
hoverMaterial : ControlTheme → Material
hoverMaterial theme = phong (ControlTheme.hoverColor theme) 32.0

-- Material for active/pressed control
activeMaterial : ControlTheme → Material
activeMaterial theme = phong (ControlTheme.activeColor theme) 32.0

-- Material for disabled control
disabledMaterial : ControlTheme → Material
disabledMaterial theme = phong (ControlTheme.disabledColor theme) 8.0
