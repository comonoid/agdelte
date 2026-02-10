{-# OPTIONS --without-K #-}

-- Agdelte.WebGL.Builder: High-level 3D scene construction DSL
--
-- This module provides a comprehensive API for building WebGL scenes:
--
-- Layout:
--   - Stack: hstack3D, vstack3D, dstack3D for linear layouts
--   - Grid: grid3D, gridAuto for 2D grids
--   - Radial: ring3D, spiral3D, sphereLayout for circular patterns
--
-- Geometry:
--   - Primitives: torus, capsule, cone, pyramid, tube, platonic solids
--   - Procedural: extrude, revolve, loft, sweep
--   - CSG: union, subtract, intersect, fillet, chamfer
--
-- Optimization:
--   - LOD: Level of detail for distance-based geometry switching
--   - Culling: Frustum and occlusion culling with bounding volumes
--   - Batching: Geometry combining and draw call optimization
--
-- Interaction:
--   - NamedParts: Sub-ID picking for complex interactive objects
--
-- Import:
--   - GLTF: Load and display 3D models

module Agdelte.WebGL.Builder where

------------------------------------------------------------------------
-- Layout modules
------------------------------------------------------------------------

open import Agdelte.WebGL.Builder.Layout.Stack public
open import Agdelte.WebGL.Builder.Layout.Grid public
open import Agdelte.WebGL.Builder.Layout.Radial public

------------------------------------------------------------------------
-- Geometry modules
------------------------------------------------------------------------

open import Agdelte.WebGL.Builder.Geometry.Primitives public
open import Agdelte.WebGL.Builder.Geometry.Procedural public
open import Agdelte.WebGL.Builder.Geometry.CSG public

------------------------------------------------------------------------
-- Optimization modules
------------------------------------------------------------------------

open import Agdelte.WebGL.Builder.Optimize.LOD public
open import Agdelte.WebGL.Builder.Optimize.Culling public
open import Agdelte.WebGL.Builder.Optimize.Batching public

------------------------------------------------------------------------
-- Interaction modules
------------------------------------------------------------------------

open import Agdelte.WebGL.Builder.Interaction.NamedParts public

------------------------------------------------------------------------
-- Import modules
------------------------------------------------------------------------

open import Agdelte.WebGL.Builder.Import.GLTF public
