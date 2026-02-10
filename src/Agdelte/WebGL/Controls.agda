{-# OPTIONS --without-K #-}

-- WebGL Controls
--
-- 3D UI controls and components for WebGL scenes.
-- Provides themed buttons, sliders, toggles, charts, gizmos, and more.
--
-- Usage:
--   open import Agdelte.WebGL.Controls
--
-- This re-exports all control modules for convenient access.

module Agdelte.WebGL.Controls where

------------------------------------------------------------------------
-- Re-export all control modules
------------------------------------------------------------------------

-- Core infrastructure
open import Agdelte.WebGL.Controls.Theme public
open import Agdelte.WebGL.Controls.State public
open import Agdelte.WebGL.Controls.Text public

-- Basic controls
open import Agdelte.WebGL.Controls.Buttons public

-- Sliders and dials
open import Agdelte.WebGL.Controls.Sliders public
  hiding (clamp01; recip; sinF; cosF; natToFloat; floatToNat; roundF)

-- Toggles, checkboxes, radio buttons
open import Agdelte.WebGL.Controls.Toggles public
  hiding (natToFloat; sinF; cosF; natEq)

-- Menus and dropdowns
open import Agdelte.WebGL.Controls.Menus public

-- Tabs and navigation
open import Agdelte.WebGL.Controls.Tabs public

------------------------------------------------------------------------
-- Input fields
------------------------------------------------------------------------

-- Input fields
open import Agdelte.WebGL.Controls.Input public
  hiding (clamp; showFloat; parseFloat)

------------------------------------------------------------------------
-- Charts
------------------------------------------------------------------------

-- 3D Charts - Bar charts
open import Agdelte.WebGL.Controls.Charts.Bar3D public
  hiding (natToFloat; maxFloat; absFloat)

-- 3D Charts - Scatter plots
open import Agdelte.WebGL.Controls.Charts.Scatter3D public
  hiding (natToFloat; _++L_)

-- 3D Charts - Surface plots
open import Agdelte.WebGL.Controls.Charts.Surface public
  hiding (natToFloat; sinF; cosF; _++L_)

-- 3D Charts - Network graphs
open import Agdelte.WebGL.Controls.Charts.Network3D public
  hiding (natToFloat; _++L_)

------------------------------------------------------------------------
-- Audio visualization
------------------------------------------------------------------------

-- Audio spectrum visualization
open import Agdelte.WebGL.Controls.Audio.Spectrum public
  hiding (natToFloat; sinF; cosF; clamp01; ltNat; _<F_; _>F_)

-- Audio waveform visualization
open import Agdelte.WebGL.Controls.Audio.Waveform public
  hiding (natToFloat; sinF; cosF; clamp; absFloat; ltNat; _<F_)

------------------------------------------------------------------------
-- Gizmos
------------------------------------------------------------------------

-- Transform manipulation gizmos
open import Agdelte.WebGL.Controls.Gizmos.Transform public
  hiding (sinF; cosF; case_of_; getPosition; getRotation; getScale)

-- Selection gizmos
open import Agdelte.WebGL.Controls.Gizmos.Selection public
  hiding (case_of_; _++L_; _<F_; _>F_)

-- Measurement gizmos
open import Agdelte.WebGL.Controls.Gizmos.Measure public
  hiding (sqrtF; atan2F; acosF; showFloat; piF; _<F_; _>F_; ltNat)

