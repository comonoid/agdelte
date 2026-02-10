{-# OPTIONS --without-K #-}

-- Optimize.Batching: Geometry combining and draw call batching
--
-- Provides utilities to merge multiple geometries into a single
-- draw call, reducing GPU overhead for complex scenes.

module Agdelte.WebGL.Builder.Optimize.Batching where

open import Data.Nat using (ℕ)
open import Data.Float using (Float)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)

open import Agdelte.WebGL.Types

------------------------------------------------------------------------
-- Static batching
------------------------------------------------------------------------

-- Combine multiple static meshes into a single geometry
-- All meshes must share the same material
-- The runtime will merge vertex buffers and render in one draw call
postulate
  combineGeometry : List Geometry → Geometry

{-# COMPILE JS combineGeometry = geometries => ({
  type: 'combined',
  geometries: geometries
}) #-}

-- Combine meshes with their transforms pre-applied
-- Useful for scene-wide static geometry
record StaticMesh : Set where
  constructor staticMesh
  field
    geometry  : Geometry
    transform : Transform

postulate
  combineStatic : List StaticMesh → Geometry

{-# COMPILE JS combineStatic = meshes => ({
  type: 'combinedStatic',
  meshes: meshes
}) #-}

------------------------------------------------------------------------
-- Material batching
------------------------------------------------------------------------

-- Group children by material for automatic batching
-- The runtime will sort and batch draw calls by material
postulate
  materialBatch : ∀ {M Msg} → List (SceneNode M Msg) → SceneNode M Msg

{-# COMPILE JS materialBatch = children => ({
  type: 'materialBatch',
  children: children
}) #-}

------------------------------------------------------------------------
-- Texture atlas batching
------------------------------------------------------------------------

-- Specify that textures should be packed into an atlas
-- Enables batching of textured objects with different images
record AtlasConfig : Set where
  constructor atlasConfig
  field
    maxSize   : ℕ      -- Maximum atlas texture size (e.g., 2048)
    padding   : ℕ      -- Pixels between textures

postulate
  textureAtlas : ∀ {M Msg} → AtlasConfig → List (SceneNode M Msg) → SceneNode M Msg

{-# COMPILE JS textureAtlas = config => children => ({
  type: 'textureAtlas',
  maxSize: Number(config.maxSize),
  padding: Number(config.padding),
  children: children
}) #-}

------------------------------------------------------------------------
-- Instance batching hints
------------------------------------------------------------------------

-- Hint that these nodes should be rendered using GPU instancing
-- The runtime will automatically merge identical geometries
postulate
  instanceHint : ∀ {M Msg} → List (SceneNode M Msg) → SceneNode M Msg

{-# COMPILE JS instanceHint = children => ({
  type: 'instanceHint',
  children: children
}) #-}

------------------------------------------------------------------------
-- Draw call sorting
------------------------------------------------------------------------

-- Sort children for optimal rendering order:
-- 1. Opaque objects front-to-back (minimize overdraw)
-- 2. Transparent objects back-to-front (correct blending)
-- 3. Group by material/shader
postulate
  optimizeDrawOrder : ∀ {M Msg} → List (SceneNode M Msg) → SceneNode M Msg

{-# COMPILE JS optimizeDrawOrder = children => ({
  type: 'sortedDrawOrder',
  children: children
}) #-}
