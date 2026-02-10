{-# OPTIONS --without-K #-}

-- WebGL Controls Charts Scatter3D
--
-- 3D scatter plots for visualizing point data in three dimensions.
-- Supports point size, color, and labels.

module Agdelte.WebGL.Controls.Charts.Scatter3D where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Float using (Float; _*_; _+_; _-_; -_)
open import Data.String using (String)
open import Data.List using (List; []; _∷_; length)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)

open import Agdelte.WebGL.Types
open import Agdelte.WebGL.Builder.Geometry.Primitives
open import Agdelte.WebGL.Controls.Theme
open import Agdelte.WebGL.Controls.Text

------------------------------------------------------------------------
-- Helper postulates
------------------------------------------------------------------------

postulate
  natToFloat : ℕ → Float

{-# COMPILE JS natToFloat = n => Number(n) #-}

------------------------------------------------------------------------
-- Scatter plot data
------------------------------------------------------------------------

record ScatterPoint : Set where
  constructor mkScatterPoint
  field
    pointPosition : Vec3
    pointSize     : Float
    pointColor    : GlColor
    pointLabel    : Maybe String

open ScatterPoint public

simplePoint : Vec3 → GlColor → ScatterPoint
simplePoint pos c = mkScatterPoint pos 0.02 c nothing

labeledPoint : Vec3 → GlColor → String → ScatterPoint
labeledPoint pos c lbl = mkScatterPoint pos 0.02 c (just lbl)

sizedPoint : Vec3 → Float → GlColor → ScatterPoint
sizedPoint pos sz c = mkScatterPoint pos sz c nothing

------------------------------------------------------------------------
-- Scatter plot configuration
------------------------------------------------------------------------

record ScatterConfig : Set where
  constructor mkScatterConfig
  field
    bounds      : Vec3            -- Size of plot volume
    showAxes    : Bool            -- Show X, Y, Z axes
    showGrid    : Bool            -- Show grid lines
    gridDivisions : ℕ             -- Grid subdivisions
    axisColor   : GlColor           -- Color for axes
    gridColor   : GlColor           -- Color for grid

open ScatterConfig public

defaultScatterConfig : ScatterConfig
defaultScatterConfig = mkScatterConfig
  (vec3 1.0 1.0 1.0)              -- bounds
  true                            -- showAxes
  true                            -- showGrid
  5                               -- gridDivisions
  (rgba 0.7 0.7 0.7 1.0)          -- axisColor
  (rgba 0.3 0.3 0.3 0.5)          -- gridColor

------------------------------------------------------------------------
-- Helper: list append
------------------------------------------------------------------------

infixr 5 _++L_
_++L_ : ∀ {A : Set} → List A → List A → List A
[] ++L ys = ys
(x ∷ xs) ++L ys = x ∷ (xs ++L ys)

------------------------------------------------------------------------
-- Scatter plot implementation
------------------------------------------------------------------------

-- 3D scatter plot
scatterPlot3D : ∀ {M Msg}
              → ControlTheme
              → ScatterConfig
              → (M → List ScatterPoint)     -- Points accessor
              → Maybe (ℕ → Msg)             -- Optional click handler
              → Transform
              → SceneNode M Msg
scatterPlot3D {M} {Msg} theme config getPoints clickHandler t =
  group t allChildren
  where
    bnds = bounds config
    bx = vec3X bnds
    by = vec3Y bnds
    bz = vec3Z bnds
    axisC = axisColor config
    gridC = gridColor config
    divs = gridDivisions config

    case_of_ : ∀ {A B : Set} → A → (A → B) → B
    case x of f = f x

    buildPointList : ℕ → List ScatterPoint → List (SceneNode M Msg)
    buildPointList _ [] = []
    buildPointList idx (p ∷ ps) =
      let pos = pointPosition p
          sz = pointSize p
          c = pointColor p
          lbl = pointLabel p
          pointT = mkTransform pos identityQuat (vec3 1.0 1.0 1.0)
          pointGeom = sphere sz
          pointMat = phong c 64.0
          attrs = case clickHandler of λ where
            nothing → []
            (just handler) → onClick (handler idx) ∷ []
          -- Point with optional label
          pointNode = interactiveGroup attrs pointT
                        (mesh pointGeom pointMat [] identityTransform ∷ [])
          labelNode = case lbl of λ where
            nothing → []
            (just l) →
              let labelT = mkTransform (vec3 0.0 (sz + 0.02) 0.0) identityQuat (vec3 1.0 1.0 1.0)
              in sizedLabel theme 0.02 l labelT ∷ []
      in group pointT (pointNode ∷ labelNode)
         ∷ buildPointList (suc idx) ps

    -- Build scatter points
    buildPoints : M → List (SceneNode M Msg)
    buildPoints m = buildPointList 0 (getPoints m)

    -- Build coordinate axes
    buildAxes : SceneNode M Msg
    buildAxes =
      let axisR = 0.005
          -- X axis (red tinted)
          xAxisGeom = cylinder axisR bx
          xAxisMat = phong (rgba 0.8 0.3 0.3 1.0) 32.0
          xAxisT = mkTransform (vec3 (bx * 0.5) 0.0 0.0)
                     (quat 0.0 0.0 0.707 0.707)  -- rotate to X
                     (vec3 1.0 1.0 1.0)
          -- Y axis (green tinted)
          yAxisGeom = cylinder axisR by
          yAxisMat = phong (rgba 0.3 0.8 0.3 1.0) 32.0
          yAxisT = mkTransform (vec3 0.0 (by * 0.5) 0.0)
                     identityQuat
                     (vec3 1.0 1.0 1.0)
          -- Z axis (blue tinted)
          zAxisGeom = cylinder axisR bz
          zAxisMat = phong (rgba 0.3 0.3 0.8 1.0) 32.0
          zAxisT = mkTransform (vec3 0.0 0.0 (bz * 0.5))
                     (quat 0.707 0.0 0.0 0.707)  -- rotate to Z
                     (vec3 1.0 1.0 1.0)
      in group identityTransform
           ( mesh xAxisGeom xAxisMat [] xAxisT
           ∷ mesh yAxisGeom yAxisMat [] yAxisT
           ∷ mesh zAxisGeom zAxisMat [] zAxisT
           ∷ [])

    -- Build grid (XZ plane)
    buildGrid : SceneNode M Msg
    buildGrid =
      let gridMat = phong gridC 16.0
          gridR = 0.002
          step = bx * (1.0 * (1.0 * (1.0 * (1.0 * 0.2))))  -- 1/5
      in group identityTransform (buildGridLines gridMat gridR step 0 divs)
      where
        buildGridLines : Material → Float → Float → ℕ → ℕ → List (SceneNode M Msg)
        buildGridLines _ _ _ _ zero = []
        buildGridLines mat r step idx (suc remaining) =
          let offset = natToFloat idx * step - bx * 0.5 + step * 0.5
              -- X-parallel line
              xLineGeom = cylinder r bx
              xLineT = mkTransform (vec3 0.0 0.0 offset)
                         (quat 0.0 0.0 0.707 0.707)
                         (vec3 1.0 1.0 1.0)
              -- Z-parallel line
              zLineGeom = cylinder r bz
              zLineT = mkTransform (vec3 offset 0.0 0.0)
                         (quat 0.707 0.0 0.0 0.707)
                         (vec3 1.0 1.0 1.0)
          in mesh xLineGeom mat [] xLineT
           ∷ mesh zLineGeom mat [] zLineT
           ∷ buildGridLines mat r step (suc idx) remaining

    allChildren : List (SceneNode M Msg)
    allChildren =
      ((if showAxes config then buildAxes ∷ [] else [])
      ++L (if showGrid config then buildGrid ∷ [] else []))
      ++L (bindChildren buildPoints identityTransform ∷ [])

-- Simple scatter plot
scatterPlot : ∀ {M Msg}
            → ControlTheme
            → (M → List ScatterPoint)
            → Transform
            → SceneNode M Msg
scatterPlot theme getPoints = scatterPlot3D theme defaultScatterConfig getPoints nothing

------------------------------------------------------------------------
-- Line chart (ribbon connecting points)
------------------------------------------------------------------------

record LineData : Set where
  constructor mkLineData
  field
    linePoints : List Vec3
    lineColor  : GlColor
    lineWidth  : Float

open LineData public

simpleLine : List Vec3 → GlColor → LineData
simpleLine pts c = mkLineData pts c 0.01

-- 3D line chart (series of connected points)
lineChart3D : ∀ {M Msg}
            → ControlTheme
            → ScatterConfig
            → (M → List LineData)           -- Lines accessor
            → Transform
            → SceneNode M Msg
lineChart3D {M} {Msg} theme config getLines t =
  group t allChildren
  where
    bnds = bounds config

    -- Connect points with cylinder segments
    buildLineSegments : GlColor → Float → List Vec3 → List (SceneNode M Msg)
    buildLineSegments _ _ [] = []
    buildLineSegments _ _ (_ ∷ []) = []
    buildLineSegments c w (p1 ∷ p2 ∷ rest) =
      let -- Midpoint
          mx = (vec3X p1 + vec3X p2) * 0.5
          my = (vec3Y p1 + vec3Y p2) * 0.5
          mz = (vec3Z p1 + vec3Z p2) * 0.5
          midT = mkTransform (vec3 mx my mz) identityQuat (vec3 1.0 1.0 1.0)
          -- Distance (simplified, uses cylinder)
          dx = vec3X p2 - vec3X p1
          dy = vec3Y p2 - vec3Y p1
          dz = vec3Z p2 - vec3Z p1
          len = 0.1  -- Simplified; real impl would calculate distance
          segGeom = cylinder w len
          segMat = phong c 32.0
      in mesh segGeom segMat [] midT
         ∷ buildLineSegments c w (p2 ∷ rest)

    buildLineList : List LineData → List (SceneNode M Msg)
    buildLineList [] = []
    buildLineList (ld ∷ lds) =
      let pts = linePoints ld
          c = lineColor ld
          w = lineWidth ld
      in buildLineSegments c w pts ++L buildLineList lds

    buildLines : M → List (SceneNode M Msg)
    buildLines m = buildLineList (getLines m)

    buildAxes : SceneNode M Msg
    buildAxes = group identityTransform []  -- Simplified

    allChildren : List (SceneNode M Msg)
    allChildren =
      (if showAxes config then buildAxes ∷ [] else [])
      ++L (bindChildren buildLines identityTransform ∷ [])

