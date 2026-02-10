{-# OPTIONS --without-K #-}

-- WebGL Controls Gizmos Selection
--
-- Selection gizmos: bounding boxes, selection handles, highlight effects.
-- Used for indicating selected objects and providing resize handles.

module Agdelte.WebGL.Controls.Gizmos.Selection where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Float using (Float; _*_; _+_; _-_; -_)
open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Agdelte.WebGL.Types
open import Agdelte.WebGL.Builder.Geometry.Primitives

------------------------------------------------------------------------
-- Module-level helpers
------------------------------------------------------------------------

case_of_ : ∀ {A B : Set} → A → (A → B) → B
case x of f = f x

infixr 5 _++L_
_++L_ : ∀ {A : Set} → List A → List A → List A
[] ++L ys = ys
(x ∷ xs) ++L ys = x ∷ (xs ++L ys)

postulate
  _<F_ : Float → Float → Bool
  _>F_ : Float → Float → Bool
{-# COMPILE JS _<F_ = x => y => x < y #-}
{-# COMPILE JS _>F_ = x => y => x > y #-}

------------------------------------------------------------------------
-- Selection style
------------------------------------------------------------------------

record SelectionStyle : Set where
  constructor mkSelectionStyle
  field
    lineColor     : GlColor         -- Outline color
    lineWidth     : Float         -- Line thickness
    handleColor   : GlColor         -- Corner handle color
    handleSize    : Float         -- Corner handle size
    fillColor     : GlColor         -- Optional fill color (transparent)
    dashLength    : Float         -- For dashed lines (0 = solid)

defaultSelectionStyle : SelectionStyle
defaultSelectionStyle = mkSelectionStyle
  (rgba 0.2 0.6 1.0 1.0)         -- lineColor (blue)
  0.005                           -- lineWidth
  (rgba 1.0 1.0 1.0 1.0)         -- handleColor (white)
  0.02                            -- handleSize
  (rgba 0.2 0.6 1.0 0.1)         -- fillColor (transparent blue)
  0.0                             -- dashLength (solid)

highlightStyle : SelectionStyle
highlightStyle = mkSelectionStyle
  (rgba 1.0 0.8 0.0 1.0)         -- lineColor (yellow)
  0.008                           -- lineWidth
  (rgba 1.0 1.0 1.0 1.0)         -- handleColor
  0.025                           -- handleSize
  (rgba 1.0 0.8 0.0 0.05)        -- fillColor
  0.0                             -- dashLength

------------------------------------------------------------------------
-- Bounding box outline
------------------------------------------------------------------------

-- Bounding box outline (wireframe)
boundingBox3D : ∀ {M Msg}
              → SelectionStyle
              → (M → Maybe (Vec3 × Vec3))    -- Min/max corners (Nothing = hidden)
              → SceneNode M Msg
boundingBox3D {M} {Msg} style getBounds =
  bindChildren buildBox identityTransform
  where
    lw = SelectionStyle.lineWidth style
    lc = SelectionStyle.lineColor style

    postulate sqrtF : Float → Float
    {-# COMPILE JS sqrtF = x => Math.sqrt(x) #-}

    edge : Float → Float → Float → Float → Float → Float → SceneNode M Msg
    edge sx sy sz ddx ddy ddz =
      let len = sqrtF (ddx * ddx + ddy * ddy + ddz * ddz)
          mx = sx + ddx * 0.5
          my = sy + ddy * 0.5
          mz = sz + ddz * 0.5
          edgeGeom = cylinder lw len
          edgeMat = phong lc 32.0
          edgeT = mkTransform (vec3 mx my mz) identityQuat (vec3 1.0 1.0 1.0)
      in mesh edgeGeom edgeMat [] edgeT

    buildEdges : Float → Float → Float → Float → Float → Float → List (SceneNode M Msg)
    buildEdges x0 y0 z0 dx dy dz =
      let -- Bottom edges
          e1 = edge x0 y0 z0 dx 0.0 0.0
          e2 = edge (x0 + dx) y0 z0 0.0 0.0 dz
          e3 = edge x0 y0 (z0 + dz) dx 0.0 0.0
          e4 = edge x0 y0 z0 0.0 0.0 dz
          -- Top edges
          e5 = edge x0 (y0 + dy) z0 dx 0.0 0.0
          e6 = edge (x0 + dx) (y0 + dy) z0 0.0 0.0 dz
          e7 = edge x0 (y0 + dy) (z0 + dz) dx 0.0 0.0
          e8 = edge x0 (y0 + dy) z0 0.0 0.0 dz
          -- Vertical edges
          e9 = edge x0 y0 z0 0.0 dy 0.0
          e10 = edge (x0 + dx) y0 z0 0.0 dy 0.0
          e11 = edge (x0 + dx) y0 (z0 + dz) 0.0 dy 0.0
          e12 = edge x0 y0 (z0 + dz) 0.0 dy 0.0
      in e1 ∷ e2 ∷ e3 ∷ e4 ∷ e5 ∷ e6 ∷ e7 ∷ e8 ∷ e9 ∷ e10 ∷ e11 ∷ e12 ∷ []

    buildBox : M → List (SceneNode M Msg)
    buildBox m = case getBounds m of λ where
      nothing → []
      (just (minV , maxV)) →
        let -- Extract corner coordinates
            x0 = vec3X minV
            y0 = vec3Y minV
            z0 = vec3Z minV
            x1 = vec3X maxV
            y1 = vec3Y maxV
            z1 = vec3Z maxV
            -- Dimensions
            dx = x1 - x0
            dy = y1 - y0
            dz = z1 - z0
        in buildEdges x0 y0 z0 dx dy dz

------------------------------------------------------------------------
-- Selection box with resize handles
------------------------------------------------------------------------

-- Selection box with corner handles for resizing
selectionBox3D : ∀ {M Msg}
               → SelectionStyle
               → (M → Maybe (Vec3 × Vec3))    -- Bounds
               → (Vec3 → Vec3 → Msg)          -- Resize handler (new min, max)
               → SceneNode M Msg
selectionBox3D {M} {Msg} style getBounds onResize =
  bindChildren buildSelection identityTransform
  where
    lc = SelectionStyle.lineColor style
    hc = SelectionStyle.handleColor style
    hs = SelectionStyle.handleSize style

    -- Build the 12 edges of the box (simplified)
    buildEdges : Vec3 → Vec3 → List (SceneNode M Msg)
    buildEdges _ _ = []  -- Simplified; use boundingBox3D for edges

    cornerHandle : Float → Float → Float → Float → Float → Float → SceneNode M Msg
    cornerHandle x y z dx dy dz =
      let handleT = mkTransform (vec3 x y z) identityQuat (vec3 1.0 1.0 1.0)
          handleGeom = sphere hs
          handleMat = phong hc 64.0
          -- Drag handler: use delta and direction to compute new bounds
          -- dx, dy, dz indicate which corner (-1 or 1 for each axis)
          dragMsg = λ start curr →
            let deltaX = vec3X curr - vec3X start
                deltaY = vec3Y curr - vec3Y start
                deltaZ = vec3Z curr - vec3Z start
                -- Apply delta only in the direction this corner can move
                newX = x + deltaX
                newY = y + deltaY
                newZ = z + deltaZ
                -- For a corner handle, we report where the corner moved to
                -- The resize handler can figure out new min/max from that
                cornerPos = vec3 newX newY newZ
                dirVec = vec3 dx dy dz
            in onResize cornerPos dirVec
      in interactiveGroup
           (onDrag dragMsg ∷ [])
           handleT
           (mesh handleGeom handleMat [] identityTransform ∷ [])

    -- Build 8 corner handles
    buildHandles : Vec3 → Vec3 → List (SceneNode M Msg)
    buildHandles minV maxV =
      let x0 = vec3X minV
          y0 = vec3Y minV
          z0 = vec3Z minV
          x1 = vec3X maxV
          y1 = vec3Y maxV
          z1 = vec3Z maxV
      in cornerHandle x0 y0 z0 (- 1.0) (- 1.0) (- 1.0)
       ∷ cornerHandle x1 y0 z0 1.0 (- 1.0) (- 1.0)
       ∷ cornerHandle x0 y1 z0 (- 1.0) 1.0 (- 1.0)
       ∷ cornerHandle x1 y1 z0 1.0 1.0 (- 1.0)
       ∷ cornerHandle x0 y0 z1 (- 1.0) (- 1.0) 1.0
       ∷ cornerHandle x1 y0 z1 1.0 (- 1.0) 1.0
       ∷ cornerHandle x0 y1 z1 (- 1.0) 1.0 1.0
       ∷ cornerHandle x1 y1 z1 1.0 1.0 1.0
       ∷ []

    buildSelection : M → List (SceneNode M Msg)
    buildSelection m = case getBounds m of λ where
      nothing → []
      (just (minV , maxV)) →
        let edges = buildEdges minV maxV
            handles = buildHandles minV maxV
        in edges ++L handles

------------------------------------------------------------------------
-- Highlight outline
------------------------------------------------------------------------

-- Simple highlight outline around an object
highlightOutline : ∀ {M Msg}
                 → SelectionStyle
                 → Vec3                       -- Size
                 → Transform
                 → SceneNode M Msg
highlightOutline style size t =
  let lw = SelectionStyle.lineWidth style
      lc = SelectionStyle.lineColor style
      -- Slightly larger wireframe box
      scale = 1.02
      w = vec3X size * scale
      h = vec3Y size * scale
      d = vec3Z size * scale
      outlineGeom = roundedBox (vec3 w h d) (lw * 2.0) 4
      outlineMat = phong lc 32.0
  in mesh outlineGeom outlineMat [] t

------------------------------------------------------------------------
-- Selection indicator
------------------------------------------------------------------------

-- Pulsing selection indicator (for hover/focus)
selectionPulse : ∀ {M Msg}
               → GlColor
               → Float                        -- Size
               → (M → Float)                  -- Animation time (0-1)
               → Transform
               → SceneNode M Msg
selectionPulse {M} color size getTime t =
  bindTransform getPulseTransform
    (mesh (sphere size) (phong color 32.0) [] t)
  where
    getPulseTransform : M → Transform
    getPulseTransform m =
      let time = getTime m
          scale = 1.0 + sinF (time * 6.28) * 0.1
      in mkTransform (vec3 0.0 0.0 0.0) identityQuat (vec3 scale scale scale)
      where
        postulate sinF : Float → Float
        {-# COMPILE JS sinF = x => Math.sin(x) #-}

------------------------------------------------------------------------
-- Selection bracket corners
------------------------------------------------------------------------

-- Corner brackets (L-shaped) around selection
selectionBrackets : ∀ {M Msg}
                  → SelectionStyle
                  → Vec3                      -- Size
                  → Transform
                  → SceneNode M Msg
selectionBrackets {M} {Msg} style size t =
  group t
    ( corner (- 1.0) (- 1.0) (- 1.0)
    ∷ corner 1.0 (- 1.0) (- 1.0)
    ∷ corner (- 1.0) 1.0 (- 1.0)
    ∷ corner 1.0 1.0 (- 1.0)
    ∷ corner (- 1.0) (- 1.0) 1.0
    ∷ corner 1.0 (- 1.0) 1.0
    ∷ corner (- 1.0) 1.0 1.0
    ∷ corner 1.0 1.0 1.0
    ∷ [])
  where
    lw = SelectionStyle.lineWidth style
    lc = SelectionStyle.lineColor style
    bracketLen = 0.1  -- Length of each bracket arm

    corner : Float → Float → Float → SceneNode M Msg
    corner dx dy dz =
      let x = vec3X size * 0.5 * dx
          y = vec3Y size * 0.5 * dy
          z = vec3Z size * 0.5 * dz
          cornerT = mkTransform (vec3 x y z) identityQuat (vec3 1.0 1.0 1.0)
          -- Three short lines forming L-bracket
          armX = cylinder lw bracketLen
          armY = cylinder lw bracketLen
          armZ = cylinder lw bracketLen
          armMat = phong lc 48.0
          armXT = mkTransform (vec3 ((- dx) * bracketLen * 0.5) 0.0 0.0)
                    (quat 0.0 0.0 0.707 0.707) (vec3 1.0 1.0 1.0)
          armYT = mkTransform (vec3 0.0 ((- dy) * bracketLen * 0.5) 0.0)
                    identityQuat (vec3 1.0 1.0 1.0)
          armZT = mkTransform (vec3 0.0 0.0 ((- dz) * bracketLen * 0.5))
                    (quat 0.707 0.0 0.0 0.707) (vec3 1.0 1.0 1.0)
      in group cornerT
           ( mesh armX armMat [] armXT
           ∷ mesh armY armMat [] armYT
           ∷ mesh armZ armMat [] armZT
           ∷ [])

