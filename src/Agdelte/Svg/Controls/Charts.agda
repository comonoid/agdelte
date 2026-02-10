{-# OPTIONS --without-K #-}

-- Agdelte.Svg.Controls.Charts: unified re-export of all SVG charts
--
-- This module provides chart components for data visualization:
-- - Line/Area charts for time series
-- - Bar charts for categorical data
-- - Pie/Donut charts for part-to-whole
-- - Scatter/Bubble for correlations
-- - Heatmap for 2D intensity
-- - Timeline for events
-- - Network for graphs
--
-- Usage:
--   open import Agdelte.Svg.Controls.Charts

module Agdelte.Svg.Controls.Charts where

------------------------------------------------------------------------
-- Line & Area Charts
------------------------------------------------------------------------

-- Line charts for time series, trends, continuous data
open import Agdelte.Svg.Controls.Charts.Line public

------------------------------------------------------------------------
-- Area Charts
------------------------------------------------------------------------

-- Area charts for filled time series and stacked data
-- (DataPoint from Line conflicts - use separate import or prefix)
open import Agdelte.Svg.Controls.Charts.Area public hiding (DataPoint; mkDataPoint; dpX; dpY)

------------------------------------------------------------------------
-- Bar Charts
------------------------------------------------------------------------

-- Bar charts for categorical comparisons
open import Agdelte.Svg.Controls.Charts.Bar public

------------------------------------------------------------------------
-- Pie & Donut Charts
------------------------------------------------------------------------

-- Pie/Donut charts for part-to-whole relationships
open import Agdelte.Svg.Controls.Charts.Pie public

------------------------------------------------------------------------
-- Scatter & Bubble Charts
------------------------------------------------------------------------

-- Scatter plots for correlation and distribution
open import Agdelte.Svg.Controls.Charts.Scatter public

------------------------------------------------------------------------
-- Heatmap
------------------------------------------------------------------------

-- Heatmaps for 2D density visualization
open import Agdelte.Svg.Controls.Charts.Heatmap public

------------------------------------------------------------------------
-- Timeline
------------------------------------------------------------------------

-- Timeline for event sequences
open import Agdelte.Svg.Controls.Charts.Timeline public

------------------------------------------------------------------------
-- Network Graph
------------------------------------------------------------------------

-- Network/Graph diagrams for node-edge data
open import Agdelte.Svg.Controls.Charts.Network public

------------------------------------------------------------------------
-- Radar/Spider Charts
------------------------------------------------------------------------

-- Radar charts for multi-dimensional comparison
open import Agdelte.Svg.Controls.Charts.Radar public

------------------------------------------------------------------------
-- Treemap
------------------------------------------------------------------------

-- Treemap for hierarchical data as nested rectangles
open import Agdelte.Svg.Controls.Charts.Treemap public

------------------------------------------------------------------------
-- Flowchart
------------------------------------------------------------------------

-- Flowchart for process flows with shaped nodes
open import Agdelte.Svg.Controls.Charts.Flowchart public

------------------------------------------------------------------------
-- Org Chart
------------------------------------------------------------------------

-- Organization chart for hierarchical structures
open import Agdelte.Svg.Controls.Charts.OrgChart public

------------------------------------------------------------------------
-- Sankey Diagram
------------------------------------------------------------------------

-- Sankey diagram for flow/transfer visualization
open import Agdelte.Svg.Controls.Charts.Sankey public
