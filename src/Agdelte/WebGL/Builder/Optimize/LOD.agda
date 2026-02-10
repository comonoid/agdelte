{-# OPTIONS --without-K #-}

-- Optimize.LOD: Level of Detail for 3D scenes
--
-- Provides automatic geometry simplification based on distance.
-- The runtime selects the appropriate detail level for each object.

module Agdelte.WebGL.Builder.Optimize.LOD where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Float using (Float)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)

open import Agdelte.WebGL.Types

------------------------------------------------------------------------
-- LOD Configuration
------------------------------------------------------------------------

-- Distance threshold for LOD switching
-- (minDistance, maxDistance) - the range where this LOD is active
record LODLevel (M Msg : Set) : Set where
  constructor lodLevel
  field
    node     : SceneNode M Msg  -- The geometry for this level
    maxDist  : Float            -- Maximum distance for this LOD

------------------------------------------------------------------------
-- LOD Node constructors
------------------------------------------------------------------------

-- LOD specification as a list of levels (sorted by distance)
-- Runtime will choose the first level whose maxDist >= distance
LODSpec : Set → Set → Set
LODSpec M Msg = List (LODLevel M Msg)

-- Create an LOD node from a specification
-- The runtime will select the appropriate level based on camera distance
postulate
  lod : ∀ {M Msg} → LODSpec M Msg → SceneNode M Msg

{-# COMPILE JS lod = levels => ({
  type: 'lod',
  levels: levels
}) #-}

------------------------------------------------------------------------
-- Convenience constructors
------------------------------------------------------------------------

-- Two-level LOD: high detail close, low detail far
lod2 : ∀ {M Msg}
     → SceneNode M Msg → Float   -- High detail, distance threshold
     → SceneNode M Msg            -- Low detail (infinite distance)
     → SceneNode M Msg
lod2 high threshold low =
  lod (lodLevel high threshold ∷ lodLevel low 999999.0 ∷ [])

-- Three-level LOD
lod3 : ∀ {M Msg}
     → SceneNode M Msg → Float   -- High detail
     → SceneNode M Msg → Float   -- Medium detail
     → SceneNode M Msg            -- Low detail
     → SceneNode M Msg
lod3 high th1 med th2 low =
  lod (lodLevel high th1 ∷ lodLevel med th2 ∷ lodLevel low 999999.0 ∷ [])

------------------------------------------------------------------------
-- Distance-based visibility
------------------------------------------------------------------------

-- Show node only within distance range
postulate
  visibleInRange : ∀ {M Msg} → Float → Float → SceneNode M Msg → SceneNode M Msg

{-# COMPILE JS visibleInRange = minDist => maxDist => node => ({
  type: 'distanceVisible',
  minDistance: minDist,
  maxDistance: maxDist,
  child: node
}) #-}

-- Fade node based on distance (alpha = 1 at near, 0 at far)
postulate
  fadeByDistance : ∀ {M Msg} → Float → Float → SceneNode M Msg → SceneNode M Msg

{-# COMPILE JS fadeByDistance = nearDist => farDist => node => ({
  type: 'distanceFade',
  nearDistance: nearDist,
  farDistance: farDist,
  child: node
}) #-}
