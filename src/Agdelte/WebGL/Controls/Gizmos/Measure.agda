{-# OPTIONS --without-K #-}

-- WebGL Controls Gizmos Measure
--
-- Measurement gizmos: distance, angle, and annotation tools.
-- Provides visual measurement aids for 3D scenes.

module Agdelte.WebGL.Controls.Gizmos.Measure where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Float using (Float; _*_; _+_; _-_; -_)
open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false; if_then_else_)

open import Agdelte.WebGL.Types
open import Agdelte.WebGL.Builder.Geometry.Primitives
open import Agdelte.WebGL.Controls.Theme
open import Agdelte.WebGL.Controls.Text

------------------------------------------------------------------------
-- Helper postulates
------------------------------------------------------------------------

postulate
  sqrtF : Float → Float
  atan2F : Float → Float → Float
  acosF : Float → Float
  showFloat : Float → String
  piF : Float
  _<F_ : Float → Float → Bool
  _>F_ : Float → Float → Bool

{-# COMPILE JS sqrtF = x => Math.sqrt(x) #-}
{-# COMPILE JS atan2F = y => x => Math.atan2(y, x) #-}
{-# COMPILE JS acosF = x => Math.acos(x) #-}
{-# COMPILE JS showFloat = x => x.toFixed(2) #-}
{-# COMPILE JS piF = Math.PI #-}
{-# COMPILE JS _<F_ = x => y => x < y #-}
{-# COMPILE JS _>F_ = x => y => x > y #-}

-- Helper for natural number comparison
ltNat : ℕ → ℕ → Bool
ltNat zero (suc _) = true
ltNat _ zero = false
ltNat (suc m) (suc n) = ltNat m n

------------------------------------------------------------------------
-- Measurement style
------------------------------------------------------------------------

record MeasureStyle : Set where
  constructor mkMeasureStyle
  field
    lineColor   : GlColor
    lineWidth   : Float
    textColor   : GlColor
    textSize    : Float
    endpointSize : Float

defaultMeasureStyle : MeasureStyle
defaultMeasureStyle = mkMeasureStyle
  (rgba 1.0 0.8 0.0 1.0)         -- lineColor (yellow)
  0.005                           -- lineWidth
  (rgba 1.0 1.0 1.0 1.0)         -- textColor
  0.03                            -- textSize
  0.01                            -- endpointSize

------------------------------------------------------------------------
-- Distance measurement
------------------------------------------------------------------------

-- Distance measurement line with label
measureDistance : ∀ {M Msg}
                → ControlTheme
                → MeasureStyle
                → Vec3                        -- Start point
                → Vec3                        -- End point
                → (Float → String)            -- Format function
                → SceneNode M Msg
measureDistance theme style p1 p2 formatDist =
  let -- Calculate distance
      dx = vec3X p2 - vec3X p1
      dy = vec3Y p2 - vec3Y p1
      dz = vec3Z p2 - vec3Z p1
      dist = sqrtF (dx * dx + dy * dy + dz * dz)
      -- Midpoint for label
      mx = (vec3X p1 + vec3X p2) * 0.5
      my = (vec3Y p1 + vec3Y p2) * 0.5
      mz = (vec3Z p1 + vec3Z p2) * 0.5
      -- Line
      lw = MeasureStyle.lineWidth style
      lc = MeasureStyle.lineColor style
      lineGeom = cylinder lw dist
      lineMat = phong lc 32.0
      lineT = mkTransform (vec3 mx my mz) identityQuat (vec3 1.0 1.0 1.0)
      -- Endpoints
      epSize = MeasureStyle.endpointSize style
      ep1Geom = sphere epSize
      ep2Geom = sphere epSize
      epMat = phong lc 48.0
      ep1T = mkTransform p1 identityQuat (vec3 1.0 1.0 1.0)
      ep2T = mkTransform p2 identityQuat (vec3 1.0 1.0 1.0)
      -- Label
      textT = mkTransform (vec3 mx (my + 0.03) mz) identityQuat (vec3 1.0 1.0 1.0)
      labelText = formatDist dist
  in group identityTransform
       ( mesh lineGeom lineMat [] lineT
       ∷ mesh ep1Geom epMat [] ep1T
       ∷ mesh ep2Geom epMat [] ep2T
       ∷ sizedLabel theme (MeasureStyle.textSize style) labelText textT
       ∷ [])

-- Simple distance with default format
simpleDistance : ∀ {M Msg}
               → ControlTheme
               → Vec3 → Vec3
               → SceneNode M Msg
simpleDistance theme p1 p2 =
  measureDistance theme defaultMeasureStyle p1 p2 defaultFormat
  where
    defaultFormat : Float → String
    defaultFormat d = showFloat d

------------------------------------------------------------------------
-- Angle measurement
------------------------------------------------------------------------

-- Angle measurement arc between three points
measureAngle : ∀ {M Msg}
             → ControlTheme
             → MeasureStyle
             → Vec3                          -- First point
             → Vec3                          -- Vertex (center)
             → Vec3                          -- Second point
             → SceneNode M Msg
measureAngle theme style p1 vertex p2 =
  let -- Vectors from vertex
      v1x = vec3X p1 - vec3X vertex
      v1y = vec3Y p1 - vec3Y vertex
      v1z = vec3Z p1 - vec3Z vertex
      v2x = vec3X p2 - vec3X vertex
      v2y = vec3Y p2 - vec3Y vertex
      v2z = vec3Z p2 - vec3Z vertex
      -- Lengths
      len1 = sqrtF (v1x * v1x + v1y * v1y + v1z * v1z)
      len2 = sqrtF (v2x * v2x + v2y * v2y + v2z * v2z)
      -- Dot product
      dot = v1x * v2x + v1y * v2y + v1z * v2z
      -- Angle in radians
      cosAngle = dot * recip (len1 * len2)
      angleRad = acosF cosAngle
      angleDeg = angleRad * 180.0 * recip piF
      -- Arc radius
      arcRadius = 0.1
      -- Style
      lw = MeasureStyle.lineWidth style
      lc = MeasureStyle.lineColor style
      -- Lines to points
      line1Geom = cylinder lw len1
      line2Geom = cylinder lw len2
      lineMat = phong lc 32.0
      m1x = (vec3X vertex + vec3X p1) * 0.5
      m1y = (vec3Y vertex + vec3Y p1) * 0.5
      m1z = (vec3Z vertex + vec3Z p1) * 0.5
      m2x = (vec3X vertex + vec3X p2) * 0.5
      m2y = (vec3Y vertex + vec3Y p2) * 0.5
      m2z = (vec3Z vertex + vec3Z p2) * 0.5
      line1T = mkTransform (vec3 m1x m1y m1z) identityQuat (vec3 1.0 1.0 1.0)
      line2T = mkTransform (vec3 m2x m2y m2z) identityQuat (vec3 1.0 1.0 1.0)
      -- Vertex marker
      vertexGeom = sphere (MeasureStyle.endpointSize style)
      vertexMat = phong lc 48.0
      vertexT = mkTransform vertex identityQuat (vec3 1.0 1.0 1.0)
      -- Arc (simplified as torus segment)
      arcGeom = torus arcRadius (lw * 0.5) 16 8
      arcMat = phong lc 32.0
      arcT = mkTransform vertex identityQuat (vec3 1.0 1.0 1.0)
      -- Angle label
      labelT = mkTransform (vec3 (vec3X vertex) (vec3Y vertex + arcRadius + 0.03) (vec3Z vertex))
                 identityQuat (vec3 1.0 1.0 1.0)
      angleText = showFloat angleDeg
  in group identityTransform
       ( mesh line1Geom lineMat [] line1T
       ∷ mesh line2Geom lineMat [] line2T
       ∷ mesh vertexGeom vertexMat [] vertexT
       ∷ mesh arcGeom arcMat [] arcT
       ∷ sizedLabel theme (MeasureStyle.textSize style) (angleText ++ "°") labelT
       ∷ [])
  where
    postulate recip : Float → Float
    postulate _++_ : String → String → String
    {-# COMPILE JS recip = x => 1 / x #-}
    {-# COMPILE JS _++_ = a => b => a + b #-}

------------------------------------------------------------------------
-- 3D annotation
------------------------------------------------------------------------

-- Text annotation in 3D space
annotation3D : ∀ {M Msg}
             → ControlTheme
             → MeasureStyle
             → Vec3                          -- Position
             → String                        -- Text
             → SceneNode M Msg
annotation3D theme style pos text =
  let textSize = MeasureStyle.textSize style
      textColor = MeasureStyle.textColor style
      -- Background panel
      padding = 0.01
      bgWidth = textSize * 4.0  -- Approximate
      bgHeight = textSize * 1.5
      bgGeom = roundedBox (vec3 bgWidth bgHeight 0.005) 0.005 4
      bgMat = phong (rgba 0.1 0.1 0.1 0.8) 16.0
      bgT = mkTransform pos identityQuat (vec3 1.0 1.0 1.0)
      -- Text
      textT = mkTransform (vec3 (vec3X pos) (vec3Y pos) (vec3Z pos + 0.006))
                identityQuat (vec3 1.0 1.0 1.0)
  in group identityTransform
       ( mesh bgGeom bgMat [] bgT
       ∷ sizedLabel theme textSize text textT
       ∷ [])

-- Annotation with leader line
annotationWithLeader : ∀ {M Msg}
                     → ControlTheme
                     → MeasureStyle
                     → Vec3                  -- Target point
                     → Vec3                  -- Label position
                     → String
                     → SceneNode M Msg
annotationWithLeader theme style target labelPos text =
  let lw = MeasureStyle.lineWidth style
      lc = MeasureStyle.lineColor style
      -- Leader line
      dx = vec3X labelPos - vec3X target
      dy = vec3Y labelPos - vec3Y target
      dz = vec3Z labelPos - vec3Z target
      len = sqrtF (dx * dx + dy * dy + dz * dz)
      mx = (vec3X target + vec3X labelPos) * 0.5
      my = (vec3Y target + vec3Y labelPos) * 0.5
      mz = (vec3Z target + vec3Z labelPos) * 0.5
      lineGeom = cylinder lw len
      lineMat = phong lc 32.0
      lineT = mkTransform (vec3 mx my mz) identityQuat (vec3 1.0 1.0 1.0)
      -- Target marker
      markerGeom = sphere (MeasureStyle.endpointSize style)
      markerMat = phong lc 48.0
      markerT = mkTransform target identityQuat (vec3 1.0 1.0 1.0)
  in group identityTransform
       ( mesh lineGeom lineMat [] lineT
       ∷ mesh markerGeom markerMat [] markerT
       ∷ annotation3D theme style labelPos text
       ∷ [])

------------------------------------------------------------------------
-- Ruler
------------------------------------------------------------------------

-- 3D ruler with tick marks
ruler3D : ∀ {M Msg}
        → ControlTheme
        → MeasureStyle
        → Vec3                              -- Start
        → Vec3                              -- End
        → Float                             -- Major tick interval
        → Float                             -- Minor tick interval
        → SceneNode M Msg
ruler3D {M} {Msg} theme style p1 p2 majorInterval minorInterval =
  let -- Direction and length
      dx = vec3X p2 - vec3X p1
      dy = vec3Y p2 - vec3Y p1
      dz = vec3Z p2 - vec3Z p1
      len = sqrtF (dx * dx + dy * dy + dz * dz)
      -- Normalize direction
      nx = dx * recip len
      ny = dy * recip len
      nz = dz * recip len
      -- Style
      lw = MeasureStyle.lineWidth style
      lc = MeasureStyle.lineColor style
      -- Main line
      mx = (vec3X p1 + vec3X p2) * 0.5
      my = (vec3Y p1 + vec3Y p2) * 0.5
      mz = (vec3Z p1 + vec3Z p2) * 0.5
      lineGeom = cylinder lw len
      lineMat = phong lc 32.0
      lineT = mkTransform (vec3 mx my mz) identityQuat (vec3 1.0 1.0 1.0)
      -- Build tick marks
      ticks = buildTicks p1 nx ny nz len 0.0 majorInterval minorInterval
  in group identityTransform
       (mesh lineGeom lineMat [] lineT ∷ ticks)
  where
    postulate recip : Float → Float
    {-# COMPILE JS recip = x => 1 / x #-}

    lw = MeasureStyle.lineWidth style
    lc = MeasureStyle.lineColor style
    majorTickLen = 0.03
    minorTickLen = 0.015

    postulate floorF : Float → Float
    postulate absF : Float → Float
    {-# COMPILE JS floorF = x => Math.floor(x) #-}
    {-# COMPILE JS absF = x => Math.abs(x) #-}

    _++L_ : List (SceneNode M Msg) → List (SceneNode M Msg) → List (SceneNode M Msg)
    [] ++L ys = ys
    (x ∷ xs) ++L ys = x ∷ (xs ++L ys)

    isMultiple : Float → Float → Bool
    isMultiple val interval =
      let ratio = val * recip interval
          rounded = floorF ratio
      in absF (ratio - rounded) <F 0.01

    -- Use ℕ counter for termination
    maxTicks : ℕ
    maxTicks = 100

    buildTicksRec : Vec3 → Float → Float → Float → Float → Float → Float → Float → ℕ → List (SceneNode M Msg)
    buildTicksRec _ _ _ _ _ _ _ _ zero = []
    buildTicksRec start nx ny nz totalLen dist majorInt minorInt (suc remaining) =
      if dist >F totalLen
        then []
        else
          let x = vec3X start + nx * dist
              y = vec3Y start + ny * dist
              z = vec3Z start + nz * dist
              isMajor = isMultiple dist majorInt
              tickLen = if isMajor then majorTickLen else minorTickLen
              tickGeom = cylinder (lw * 0.5) tickLen
              tickMat = phong lc 32.0
              -- Perpendicular direction (simplified: use Y)
              tickT = mkTransform (vec3 x (y + tickLen * 0.5) z) identityQuat (vec3 1.0 1.0 1.0)
              tickNode = mesh tickGeom tickMat [] tickT
              -- Label at major ticks
              labelNodes = if isMajor
                then (sizedLabel theme (MeasureStyle.textSize style * 0.7) (showFloat dist)
                       (mkTransform (vec3 x (y + tickLen + 0.02) z) identityQuat (vec3 1.0 1.0 1.0))
                     ∷ [])
                else []
          in tickNode ∷ labelNodes ++L buildTicksRec start nx ny nz totalLen (dist + minorInt) majorInt minorInt remaining

    buildTicks : Vec3 → Float → Float → Float → Float → Float → Float → Float → List (SceneNode M Msg)
    buildTicks start nx ny nz totalLen dist majorInt minorInt =
      buildTicksRec start nx ny nz totalLen dist majorInt minorInt maxTicks

------------------------------------------------------------------------
-- Grid plane
------------------------------------------------------------------------

-- Reference grid plane
gridPlane : ∀ {M Msg}
          → MeasureStyle
          → Float                           -- Size
          → Float                           -- Cell size
          → Transform
          → SceneNode M Msg
gridPlane {M} {Msg} style size cellSize t =
  group t (buildGridRec 0 numLines)
  where
    lw = MeasureStyle.lineWidth style * 0.5
    lc = MeasureStyle.lineColor style

    postulate natToFloat : ℕ → Float
    {-# COMPILE JS natToFloat = n => Number(n) #-}

    numLines : ℕ
    numLines = 20  -- Simplified; would calculate from size/cellSize

    -- Use remaining count for termination
    buildGridRec : ℕ → ℕ → List (SceneNode M Msg)
    buildGridRec _ zero = []
    buildGridRec n (suc remaining) =
      let offset = (natToFloat n - natToFloat numLines * 0.5) * cellSize
          -- Horizontal line
          hLineGeom = cylinder lw size
          hLineMat = phong lc 16.0
          hLineT = mkTransform (vec3 0.0 0.0 offset)
                     (quat 0.0 0.0 0.707 0.707)
                     (vec3 1.0 1.0 1.0)
          -- Vertical line
          vLineGeom = cylinder lw size
          vLineMat = phong lc 16.0
          vLineT = mkTransform (vec3 offset 0.0 0.0)
                     (quat 0.707 0.0 0.0 0.707)
                     (vec3 1.0 1.0 1.0)
      in mesh hLineGeom hLineMat [] hLineT
       ∷ mesh vLineGeom vLineMat [] vLineT
       ∷ buildGridRec (suc n) remaining

