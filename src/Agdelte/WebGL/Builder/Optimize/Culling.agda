{-# OPTIONS --without-K #-}

-- Optimize.Culling: Frustum and occlusion culling
--
-- Provides scene-level optimizations to avoid rendering objects
-- that are not visible to the camera.

module Agdelte.WebGL.Builder.Optimize.Culling where

open import Data.Float using (Float)
open import Data.List using (List)

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
postulate
  withBounds : ∀ {M Msg} → AABB → SceneNode M Msg → SceneNode M Msg

{-# COMPILE JS withBounds = bounds => node => ({
  type: 'bounded',
  bounds: { min: bounds.min, max: bounds.max },
  child: node
}) #-}

-- Attach a bounding sphere for frustum culling
-- Faster than box culling, but less precise
postulate
  withSphereBounds : ∀ {M Msg} → BoundingSphere → SceneNode M Msg → SceneNode M Msg

{-# COMPILE JS withSphereBounds = sphere => node => ({
  type: 'sphereBounded',
  center: sphere.sphereCenter,
  radius: sphere.sphereRadius,
  child: node
}) #-}

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
postulate
  autoBounds : ∀ {M Msg} → SceneNode M Msg → SceneNode M Msg

{-# COMPILE JS autoBounds = node => ({
  type: 'autoBounded',
  child: node
}) #-}

------------------------------------------------------------------------
-- Occlusion culling
------------------------------------------------------------------------

-- Mark node as an occluder (can hide things behind it)
-- The runtime uses these for occlusion queries
postulate
  occluder : ∀ {M Msg} → SceneNode M Msg → SceneNode M Msg

{-# COMPILE JS occluder = node => ({
  type: 'occluder',
  child: node
}) #-}

-- Mark node as occludee (can be hidden by occluders)
postulate
  occludee : ∀ {M Msg} → SceneNode M Msg → SceneNode M Msg

{-# COMPILE JS occludee = node => ({
  type: 'occludee',
  child: node
}) #-}

------------------------------------------------------------------------
-- Portal culling (for indoor scenes)
------------------------------------------------------------------------

-- Define a portal (doorway/window) between two spaces
-- Only render content through portal if portal is visible
postulate
  portal : ∀ {M Msg}
         → Vec3             -- Portal center
         → Vec3             -- Portal size (width, height, 0)
         → SceneNode M Msg  -- Content visible through portal
         → SceneNode M Msg

{-# COMPILE JS portal = center => size => content => ({
  type: 'portal',
  center: center,
  size: size,
  child: content
}) #-}

------------------------------------------------------------------------
-- Spatial partitioning hints
------------------------------------------------------------------------

-- Hint that children are spatially organized as an octree
-- Enables faster culling of large scenes
postulate
  octreeHint : ∀ {M Msg} → List (SceneNode M Msg) → SceneNode M Msg

{-# COMPILE JS octreeHint = children => ({
  type: 'octreeHint',
  children: children
}) #-}
