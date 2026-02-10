{-# OPTIONS --without-K #-}

-- Agdelte.Svg.Controls: unified re-export of all SVG controls
--
-- This module provides a comprehensive library of SVG-based UI controls
-- for building dashboards, data visualizations, and interactive graphics.
--
-- Usage:
--   open import Agdelte.Svg.Controls
--
-- Or import individual modules:
--   open import Agdelte.Svg.Controls.Button
--   open import Agdelte.Svg.Controls.Slider
--   etc.

module Agdelte.Svg.Controls where

------------------------------------------------------------------------
-- Form Controls
------------------------------------------------------------------------

-- Button: clickable buttons with hover/active states
open import Agdelte.Svg.Controls.Button public

-- Slider: horizontal/vertical value sliders
open import Agdelte.Svg.Controls.Slider public

-- RangeSlider: dual-thumb min/max range selection
open import Agdelte.Svg.Controls.RangeSlider public

-- Checkbox: toggle checkboxes with checkmark indicator
open import Agdelte.Svg.Controls.Checkbox public

-- Toggle: iOS-style on/off switches
open import Agdelte.Svg.Controls.Toggle public

-- RadioGroup: single-select radio buttons and segmented controls
open import Agdelte.Svg.Controls.RadioGroup public

-- Knob: rotary dial controls (like volume knobs)
open import Agdelte.Svg.Controls.Knob public

------------------------------------------------------------------------
-- Data Display
------------------------------------------------------------------------

-- Progress: linear and circular progress indicators
open import Agdelte.Svg.Controls.Progress public

-- Gauge: speedometer-style gauge displays
open import Agdelte.Svg.Controls.Gauge public

-- Sparkline: mini inline charts for trends
open import Agdelte.Svg.Controls.Sparkline public

------------------------------------------------------------------------
-- Chart Components
------------------------------------------------------------------------

-- Legend: chart legends with color/shape indicators
open import Agdelte.Svg.Controls.Legend public

-- Axis: X and Y axes with tick marks and labels
open import Agdelte.Svg.Controls.Axis public

------------------------------------------------------------------------
-- Charts (Data Visualization)
------------------------------------------------------------------------

-- Full chart types: Line, Area, Bar, Pie, Scatter, Heatmap, Timeline, Network, Radar
open import Agdelte.Svg.Controls.Charts public

------------------------------------------------------------------------
-- Gauges & Indicators
------------------------------------------------------------------------

-- Gauge, Sparkline, and ProgressRing from Gauges module
open import Agdelte.Svg.Controls.Gauges public

------------------------------------------------------------------------
-- Layout & Interaction
------------------------------------------------------------------------

-- Tooltip: positioned tooltips and badges
open import Agdelte.Svg.Controls.Tooltip public

-- Connector: lines between elements for diagrams
open import Agdelte.Svg.Controls.Connector public

-- Draggable: drag handles and selection boxes
open import Agdelte.Svg.Controls.Draggable public

------------------------------------------------------------------------
-- Icons
------------------------------------------------------------------------

-- Icon library with common UI icons
-- (use separate import to avoid name conflicts with Button)
-- open import Agdelte.Svg.Controls.Icons
