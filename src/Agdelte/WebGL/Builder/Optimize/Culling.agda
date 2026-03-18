{-# OPTIONS --without-K #-}

-- Optimize.Culling: Frustum and occlusion culling
--
-- Provides scene-level optimizations to avoid rendering objects
-- that are not visible to the camera.

module Agdelte.WebGL.Builder.Optimize.Culling where

open import Data.Float using (Float)
open import Data.List using (List; []; _∷_)
open import Data.String using (String)

open import Agdelte.WebGL.Types

------------------------------------------------------------------------
-- Bounding volumes
------------------------------------------------------------------------

-- Axis-aligned bounding box
record AABB : Set where
  constructor aabb
  field
    min : Vec3  -- Minimum corner
    max : Vec3  -- Maximum corner

-- Bounding sphere
record BoundingSphere : Set where
  constructor boundingSphere
  field
    sphereCenter : Vec3
    sphereRadius : Float

------------------------------------------------------------------------
-- Culling nodes
------------------------------------------------------------------------

-- Attach a bounding box for frustum culling
-- Runtime will skip rendering if the box is outside the view frustum
-- Wrapped in named/group so zoomSceneNode can traverse it
postulate
  withBoundsRaw : ∀ {M Msg} → AABB → SceneNode M Msg → SceneNode M Msg

{-# COMPILE JS withBoundsRaw = bounds => node =>
  bounds(min => max => ({
    type: 'bounded',
    bounds: { min: min, max: max },
    child: node
  })) #-}

withBounds : ∀ {M Msg} → AABB → SceneNode M Msg → SceneNode M Msg
withBounds b child = named "optimizationHint" (group identityTransform (withBoundsRaw b child ∷ []))

-- Attach a bounding sphere for frustum culling
-- Faster than box culling, but less precise
-- Wrapped in named/group so zoomSceneNode can traverse it
postulate
  withSphereBoundsRaw : ∀ {M Msg} → BoundingSphere → SceneNode M Msg → SceneNode M Msg

{-# COMPILE JS withSphereBoundsRaw = sphere => node =>
  sphere(center => radius => ({
    type: 'sphereBounded',
    center: center,
    radius: radius,
    child: node
  })) #-}

withSphereBounds : ∀ {M Msg} → BoundingSphere → SceneNode M Msg → SceneNode M Msg
withSphereBounds s child = named "optimizationHint" (group identityTransform (withSphereBoundsRaw s child ∷ []))

------------------------------------------------------------------------
-- Convenience functions for common bounding volumes
------------------------------------------------------------------------

-- Create AABB from center and half-extents
aabbFromCenter : Vec3 → Vec3 → AABB
aabbFromCenter c halfExtents =
  aabb (vec3 (vec3X c - vec3X halfExtents)
             (vec3Y c - vec3Y halfExtents)
             (vec3Z c - vec3Z halfExtents))
       (vec3 (vec3X c + vec3X halfExtents)
             (vec3Y c + vec3Y halfExtents)
             (vec3Z c + vec3Z halfExtents))
  where
    open import Data.Float using (_+_; _-_)

-- Create bounding sphere from center and radius
sphereFromCenter : Vec3 → Float → BoundingSphere
sphereFromCenter c r = boundingSphere c r

------------------------------------------------------------------------
-- Auto-bounding (runtime computes bounds from geometry)
------------------------------------------------------------------------

-- Let runtime compute bounding box from child geometry
-- Wrapped in named/group so zoomSceneNode can traverse it
postulate
  autoBoundsRaw : ∀ {M Msg} → SceneNode M Msg → SceneNode M Msg

{-# COMPILE JS autoBoundsRaw = node => ({
  type: 'autoBounded',
  child: node
}) #-}

autoBounds : ∀ {M Msg} → SceneNode M Msg → SceneNode M Msg
autoBounds child = named "optimizationHint" (group identityTransform (autoBoundsRaw child ∷ []))

------------------------------------------------------------------------
-- Occlusion culling
------------------------------------------------------------------------

-- Mark node as an occluder (can hide things behind it)
-- The runtime uses these for occlusion queries
-- Wrapped in named/group so zoomSceneNode can traverse it
postulate
  occluderRaw : ∀ {M Msg} → SceneNode M Msg → SceneNode M Msg

{-# COMPILE JS occluderRaw = node => ({
  type: 'occluder',
  child: node
}) #-}

occluder : ∀ {M Msg} → SceneNode M Msg → SceneNode M Msg
occluder child = named "optimizationHint" (group identityTransform (occluderRaw child ∷ []))

-- Mark node as occludee (can be hidden by occluders)
-- Wrapped in named/group so zoomSceneNode can traverse it
postulate
  occludeeRaw : ∀ {M Msg} → SceneNode M Msg → SceneNode M Msg

{-# COMPILE JS occludeeRaw = node => ({
  type: 'occludee',
  child: node
}) #-}

occludee : ∀ {M Msg} → SceneNode M Msg → SceneNode M Msg
occludee child = named "optimizationHint" (group identityTransform (occludeeRaw child ∷ []))

------------------------------------------------------------------------
-- Portal culling (for indoor scenes)
------------------------------------------------------------------------

-- Define a portal (doorway/window) between two spaces
-- Only render content through portal if portal is visible
-- Wrapped in named/group so zoomSceneNode can traverse it
postulate
  portalRaw : ∀ {M Msg}
            → Vec3             -- Portal center
            → Vec3             -- Portal size (width, height, 0)
            → SceneNode M Msg  -- Content visible through portal
            → SceneNode M Msg

{-# COMPILE JS portalRaw = center => size => content => ({
  type: 'portal',
  center: center,
  size: size,
  child: content
}) #-}

portal : ∀ {M Msg} → Vec3 → Vec3 → SceneNode M Msg → SceneNode M Msg
portal c s child = named "optimizationHint" (group identityTransform (portalRaw c s child ∷ []))

------------------------------------------------------------------------
-- Spatial partitioning hints
------------------------------------------------------------------------

-- Hint that children are spatially organized as an octree
-- Enables faster culling of large scenes
-- Wrapped in named/group so zoomSceneNode can traverse it
postulate
  octreeHintRaw : ∀ {M Msg} → List (SceneNode M Msg) → SceneNode M Msg

{-# COMPILE JS octreeHintRaw = children => ({
  type: 'octreeHint',
  children: children
}) #-}

octreeHint : ∀ {M Msg} → List (SceneNode M Msg) → SceneNode M Msg
octreeHint children = named "optimizationHint" (group identityTransform (octreeHintRaw children ∷ []))
