{-# OPTIONS --without-K #-}

-- WebGL Controls Gizmos Transform
--
-- Transform manipulation gizmos: translate, rotate, scale.
-- Provides interactive handles for 3D object manipulation.

module Agdelte.WebGL.Controls.Gizmos.Transform where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Float using (Float; _*_; _+_; _-_; -_)
open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false; if_then_else_)

open import Agdelte.WebGL.Types
open import Agdelte.WebGL.Builder.Geometry.Primitives

------------------------------------------------------------------------
-- Helper postulates
------------------------------------------------------------------------

postulate
  sinF : Float → Float
  cosF : Float → Float

{-# COMPILE JS sinF = x => Math.sin(x) #-}
{-# COMPILE JS cosF = x => Math.cos(x) #-}

-- Module-level case helper
case_of_ : ∀ {A B : Set} → A → (A → B) → B
case x of f = f x

-- Transform field accessors
getPosition : Transform → Vec3
getPosition (mkTransform pos _ _) = pos

getRotation : Transform → Quat
getRotation (mkTransform _ rot _) = rot

getScale : Transform → Vec3
getScale (mkTransform _ _ sc) = sc

------------------------------------------------------------------------
-- Gizmo configuration
------------------------------------------------------------------------

record GizmoStyle : Set where
  constructor mkGizmoStyle
  field
    size        : Float           -- Gizmo size
    lineWidth   : Float           -- Arrow/ring thickness
    xColor      : GlColor           -- X axis color (red)
    yColor      : GlColor           -- Y axis color (green)
    zColor      : GlColor           -- Z axis color (blue)
    hoverColor  : GlColor           -- Highlighted color
    centerColor : GlColor           -- Center sphere color

defaultGizmoStyle : GizmoStyle
defaultGizmoStyle = mkGizmoStyle
  0.3                             -- size
  0.01                            -- lineWidth
  (rgba 0.9 0.2 0.2 1.0)         -- xColor (red)
  (rgba 0.2 0.9 0.2 1.0)         -- yColor (green)
  (rgba 0.2 0.2 0.9 1.0)         -- zColor (blue)
  (rgba 1.0 1.0 0.3 1.0)         -- hoverColor (yellow)
  (rgba 0.8 0.8 0.8 1.0)         -- centerColor

data GizmoMode : Set where
  TranslateMode : GizmoMode
  RotateMode    : GizmoMode
  ScaleMode     : GizmoMode

------------------------------------------------------------------------
-- Translation gizmo
------------------------------------------------------------------------

-- Translation gizmo with XYZ arrows
translateGizmo : ∀ {M Msg}
               → GizmoStyle
               → (M → Vec3)                   -- Current position
               → (Vec3 → Msg)                 -- Position update
               → SceneNode M Msg
translateGizmo {M} {Msg} style getPosition updatePosition =
  bindTransform (λ m → mkTransform (getPosition m) identityQuat (vec3 1.0 1.0 1.0))
    (group identityTransform
      ( centerSphere
      ∷ xArrow
      ∷ yArrow
      ∷ zArrow
      ∷ []))
  where
    sz = GizmoStyle.size style
    lw = GizmoStyle.lineWidth style
    xC = GizmoStyle.xColor style
    yC = GizmoStyle.yColor style
    zC = GizmoStyle.zColor style
    cC = GizmoStyle.centerColor style

    -- Center sphere
    centerSphere : SceneNode M Msg
    centerSphere =
      let geom = sphere (lw * 2.0)
          mat = phong cC 64.0
      in mesh geom mat [] identityTransform

    -- X axis arrow (red, pointing right)
    xArrow : SceneNode M Msg
    xArrow =
      let -- Shaft
          shaftGeom = cylinder lw (sz * 0.8)
          shaftMat = phong xC 48.0
          shaftT = mkTransform (vec3 (sz * 0.4) 0.0 0.0)
                     (quat 0.0 0.0 0.707 0.707)  -- Rotate to X
                     (vec3 1.0 1.0 1.0)
          -- Cone head
          coneGeom = cone' (lw * 3.0) (sz * 0.2)
          coneMat = phong xC 48.0
          coneT = mkTransform (vec3 (sz * 0.9) 0.0 0.0)
                    (quat 0.0 0.0 0.707 0.707)
                    (vec3 1.0 1.0 1.0)
          -- Interaction: start is drag start pos, curr is current drag pos
          -- Only move along X axis (delta between start and current)
          dragMsg = λ start curr →
            let deltaX = vec3X curr - vec3X start
            in updatePosition (vec3 deltaX 0.0 0.0)
      in interactiveGroup
           (onDrag dragMsg ∷ [])
           identityTransform
           ( mesh shaftGeom shaftMat [] shaftT
           ∷ mesh coneGeom coneMat [] coneT
           ∷ [])

    -- Y axis arrow (green, pointing up)
    yArrow : SceneNode M Msg
    yArrow =
      let shaftGeom = cylinder lw (sz * 0.8)
          shaftMat = phong yC 48.0
          shaftT = mkTransform (vec3 0.0 (sz * 0.4) 0.0)
                     identityQuat
                     (vec3 1.0 1.0 1.0)
          coneGeom = cone' (lw * 3.0) (sz * 0.2)
          coneMat = phong yC 48.0
          coneT = mkTransform (vec3 0.0 (sz * 0.9) 0.0)
                    identityQuat
                    (vec3 1.0 1.0 1.0)
          dragMsg = λ start curr →
            let deltaY = vec3Y curr - vec3Y start
            in updatePosition (vec3 0.0 deltaY 0.0)
      in interactiveGroup
           (onDrag dragMsg ∷ [])
           identityTransform
           ( mesh shaftGeom shaftMat [] shaftT
           ∷ mesh coneGeom coneMat [] coneT
           ∷ [])

    -- Z axis arrow (blue, pointing forward)
    zArrow : SceneNode M Msg
    zArrow =
      let shaftGeom = cylinder lw (sz * 0.8)
          shaftMat = phong zC 48.0
          shaftT = mkTransform (vec3 0.0 0.0 (sz * 0.4))
                     (quat 0.707 0.0 0.0 0.707)  -- Rotate to Z
                     (vec3 1.0 1.0 1.0)
          coneGeom = cone' (lw * 3.0) (sz * 0.2)
          coneMat = phong zC 48.0
          coneT = mkTransform (vec3 0.0 0.0 (sz * 0.9))
                    (quat 0.707 0.0 0.0 0.707)
                    (vec3 1.0 1.0 1.0)
          dragMsg = λ start curr →
            let deltaZ = vec3Z curr - vec3Z start
            in updatePosition (vec3 0.0 0.0 deltaZ)
      in interactiveGroup
           (onDrag dragMsg ∷ [])
           identityTransform
           ( mesh shaftGeom shaftMat [] shaftT
           ∷ mesh coneGeom coneMat [] coneT
           ∷ [])

------------------------------------------------------------------------
-- Rotation gizmo
------------------------------------------------------------------------

-- Rotation gizmo with XYZ rings
rotateGizmo : ∀ {M Msg}
            → GizmoStyle
            → (M → Quat)                     -- Current rotation
            → (Quat → Msg)                   -- Rotation update
            → SceneNode M Msg
rotateGizmo {M} {Msg} style getRotation updateRotation =
  group identityTransform
    ( xRing
    ∷ yRing
    ∷ zRing
    ∷ [])
  where
    sz = GizmoStyle.size style
    lw = GizmoStyle.lineWidth style
    xC = GizmoStyle.xColor style
    yC = GizmoStyle.yColor style
    zC = GizmoStyle.zColor style

    -- X rotation ring (red, around X axis = YZ plane)
    xRing : SceneNode M Msg
    xRing =
      let ringGeom = torus sz lw 32 12
          ringMat = phong xC 48.0
          -- Ring in YZ plane (default torus is XY, rotate 90° around Y)
          ringT = mkTransform (vec3 0.0 0.0 0.0)
                    (quat 0.0 0.707 0.0 0.707)
                    (vec3 1.0 1.0 1.0)
          dragMsg = λ start curr →
            let deltaY = vec3Y curr - vec3Y start
                angle = deltaY * 0.01  -- Convert drag delta to angle
                halfA = angle * 0.5
            in updateRotation (quat (sinF halfA) 0.0 0.0 (cosF halfA))
      in interactiveGroup
           (onDrag dragMsg ∷ [])
           ringT
           (mesh ringGeom ringMat [] identityTransform ∷ [])

    -- Y rotation ring (green, around Y axis = XZ plane)
    yRing : SceneNode M Msg
    yRing =
      let ringGeom = torus sz lw 32 12
          ringMat = phong yC 48.0
          -- Ring in XZ plane (default is XY, rotate 90° around X)
          ringT = mkTransform (vec3 0.0 0.0 0.0)
                    (quat 0.707 0.0 0.0 0.707)
                    (vec3 1.0 1.0 1.0)
          dragMsg = λ start curr →
            let deltaX = vec3X curr - vec3X start
                angle = deltaX * 0.01
                halfA = angle * 0.5
            in updateRotation (quat 0.0 (sinF halfA) 0.0 (cosF halfA))
      in interactiveGroup
           (onDrag dragMsg ∷ [])
           ringT
           (mesh ringGeom ringMat [] identityTransform ∷ [])

    -- Z rotation ring (blue, around Z axis = XY plane)
    zRing : SceneNode M Msg
    zRing =
      let ringGeom = torus sz lw 32 12
          ringMat = phong zC 48.0
          -- Ring already in XY plane
          ringT = identityTransform
          dragMsg = λ start curr →
            let deltaX = vec3X curr - vec3X start
                angle = deltaX * 0.01
                halfA = angle * 0.5
            in updateRotation (quat 0.0 0.0 (sinF halfA) (cosF halfA))
      in interactiveGroup
           (onDrag dragMsg ∷ [])
           ringT
           (mesh ringGeom ringMat [] identityTransform ∷ [])

------------------------------------------------------------------------
-- Scale gizmo
------------------------------------------------------------------------

-- Scale gizmo with XYZ boxes
scaleGizmo : ∀ {M Msg}
           → GizmoStyle
           → (M → Vec3)                      -- Current scale
           → (Vec3 → Msg)                    -- Scale update
           → SceneNode M Msg
scaleGizmo {M} {Msg} style getScale updateScale =
  group identityTransform
    ( centerCube
    ∷ xHandle
    ∷ yHandle
    ∷ zHandle
    ∷ [])
  where
    sz = GizmoStyle.size style
    lw = GizmoStyle.lineWidth style
    xC = GizmoStyle.xColor style
    yC = GizmoStyle.yColor style
    zC = GizmoStyle.zColor style
    cC = GizmoStyle.centerColor style

    handleSize = lw * 4.0

    -- Center cube (uniform scale)
    centerCube : SceneNode M Msg
    centerCube =
      let geom = roundedBox (vec3 (handleSize * 1.5) (handleSize * 1.5) (handleSize * 1.5)) 0.002 4
          mat = phong cC 48.0
          dragMsg = λ start curr →
            let deltaX = vec3X curr - vec3X start
                s = 1.0 + deltaX * 0.01
            in updateScale (vec3 s s s)
      in interactiveGroup
           (onDrag dragMsg ∷ [])
           identityTransform
           (mesh geom mat [] identityTransform ∷ [])

    -- X scale handle (red box on X axis)
    xHandle : SceneNode M Msg
    xHandle =
      let -- Line to handle
          lineGeom = cylinder lw (sz * 0.7)
          lineMat = phong xC 48.0
          lineT = mkTransform (vec3 (sz * 0.35) 0.0 0.0)
                    (quat 0.0 0.0 0.707 0.707)
                    (vec3 1.0 1.0 1.0)
          -- Box handle
          boxGeom = roundedBox (vec3 handleSize handleSize handleSize) 0.002 4
          boxMat = phong xC 48.0
          boxT = mkTransform (vec3 (sz * 0.8) 0.0 0.0)
                   identityQuat
                   (vec3 1.0 1.0 1.0)
          dragMsg = λ start curr →
            let deltaX = vec3X curr - vec3X start
                s = 1.0 + deltaX * 0.01
            in updateScale (vec3 s 1.0 1.0)
      in interactiveGroup
           (onDrag dragMsg ∷ [])
           identityTransform
           ( mesh lineGeom lineMat [] lineT
           ∷ mesh boxGeom boxMat [] boxT
           ∷ [])

    -- Y scale handle (green box on Y axis)
    yHandle : SceneNode M Msg
    yHandle =
      let lineGeom = cylinder lw (sz * 0.7)
          lineMat = phong yC 48.0
          lineT = mkTransform (vec3 0.0 (sz * 0.35) 0.0)
                    identityQuat
                    (vec3 1.0 1.0 1.0)
          boxGeom = roundedBox (vec3 handleSize handleSize handleSize) 0.002 4
          boxMat = phong yC 48.0
          boxT = mkTransform (vec3 0.0 (sz * 0.8) 0.0)
                   identityQuat
                   (vec3 1.0 1.0 1.0)
          dragMsg = λ start curr →
            let deltaY = vec3Y curr - vec3Y start
                s = 1.0 + deltaY * 0.01
            in updateScale (vec3 1.0 s 1.0)
      in interactiveGroup
           (onDrag dragMsg ∷ [])
           identityTransform
           ( mesh lineGeom lineMat [] lineT
           ∷ mesh boxGeom boxMat [] boxT
           ∷ [])

    -- Z scale handle (blue box on Z axis)
    zHandle : SceneNode M Msg
    zHandle =
      let lineGeom = cylinder lw (sz * 0.7)
          lineMat = phong zC 48.0
          lineT = mkTransform (vec3 0.0 0.0 (sz * 0.35))
                    (quat 0.707 0.0 0.0 0.707)
                    (vec3 1.0 1.0 1.0)
          boxGeom = roundedBox (vec3 handleSize handleSize handleSize) 0.002 4
          boxMat = phong zC 48.0
          boxT = mkTransform (vec3 0.0 0.0 (sz * 0.8))
                   identityQuat
                   (vec3 1.0 1.0 1.0)
          dragMsg = λ start curr →
            let deltaZ = vec3Z curr - vec3Z start
                s = 1.0 + deltaZ * 0.01
            in updateScale (vec3 1.0 1.0 s)
      in interactiveGroup
           (onDrag dragMsg ∷ [])
           identityTransform
           ( mesh lineGeom lineMat [] lineT
           ∷ mesh boxGeom boxMat [] boxT
           ∷ [])

------------------------------------------------------------------------
-- Combined transform gizmo
------------------------------------------------------------------------

-- Combined gizmo that shows translate, rotate, or scale based on mode
transformGizmo : ∀ {M Msg}
               → GizmoStyle
               → (M → GizmoMode)              -- Current mode
               → (M → Transform)              -- Object transform
               → (Transform → Msg)            -- Transform update
               → SceneNode M Msg
transformGizmo {M} {Msg} style getMode getTransform updateTransform =
  bindChildren selectGizmo identityTransform
  where
    selectGizmo : M → List (SceneNode M Msg)
    selectGizmo m = case getMode m of λ where
      TranslateMode →
        translateGizmo style
          (λ m' → getPosition (getTransform m'))
          (λ pos → updateTransform (mkTransform pos
                     (getRotation (getTransform m))
                     (getScale (getTransform m))))
        ∷ []
      RotateMode →
        rotateGizmo style
          (λ m' → getRotation (getTransform m'))
          (λ rot → updateTransform (mkTransform
                     (getPosition (getTransform m))
                     rot
                     (getScale (getTransform m))))
        ∷ []
      ScaleMode →
        scaleGizmo style
          (λ m' → getScale (getTransform m'))
          (λ sc → updateTransform (mkTransform
                    (getPosition (getTransform m))
                    (getRotation (getTransform m))
                    sc))
        ∷ []
