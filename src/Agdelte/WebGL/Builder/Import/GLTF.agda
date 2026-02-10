{-# OPTIONS --without-K #-}

-- Import.GLTF: GLTF/GLB model loading
--
-- Provides functions to load and display 3D models in GLTF format.
-- Supports both .gltf (JSON + external files) and .glb (binary) formats.

module Agdelte.WebGL.Builder.Import.GLTF where

open import Data.String using (String)
open import Data.List using (List; [])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (Bool)
open import Data.Float using (Float)

open import Agdelte.WebGL.Types

------------------------------------------------------------------------
-- Model handle (opaque reference to loaded model)
------------------------------------------------------------------------

-- Handle to a loaded GLTF model
-- The actual model data is managed by the runtime
postulate
  ModelHandle : Set

------------------------------------------------------------------------
-- Model loading
------------------------------------------------------------------------

-- Load a GLTF/GLB model from URL
-- Returns a handle that can be used to create scene nodes
postulate
  loadModel : String → ModelHandle

{-# COMPILE JS loadModel = url => ({
  type: 'modelHandle',
  url: url,
  format: 'gltf'
}) #-}

-- Load with options
record LoadOptions : Set where
  constructor loadOptions
  field
    receiveShadows : Bool
    castShadows    : Bool

postulate
  loadModelWith : LoadOptions → String → ModelHandle

{-# COMPILE JS loadModelWith = options => url => ({
  type: 'modelHandle',
  url: url,
  format: 'gltf',
  options: options
}) #-}

------------------------------------------------------------------------
-- Model scene nodes
------------------------------------------------------------------------

-- Create a scene node from a loaded model
-- Renders the entire model with default materials
postulate
  model : ∀ {M Msg}
        → ModelHandle
        → List (SceneAttr Msg)
        → Transform
        → SceneNode M Msg

{-# COMPILE JS model = handle => attrs => transform => ({
  type: 'model',
  handle: handle,
  attrs: attrs,
  transform: transform
}) #-}

-- Create a scene node from a specific node within the model
-- name: the name of the node in the GLTF scene graph
postulate
  modelNode : ∀ {M Msg}
            → ModelHandle
            → String
            → List (SceneAttr Msg)
            → Transform
            → SceneNode M Msg

{-# COMPILE JS modelNode = handle => nodeName => attrs => transform => ({
  type: 'modelNode',
  handle: handle,
  nodeName: nodeName,
  attrs: attrs,
  transform: transform
}) #-}

-- Create geometry from a mesh within the model
postulate
  meshGeometry : ModelHandle → String → Geometry

{-# COMPILE JS meshGeometry = handle => meshName => ({
  type: 'modelMesh',
  handle: handle,
  meshName: meshName
}) #-}

------------------------------------------------------------------------
-- Animations
------------------------------------------------------------------------

-- Play an animation from the model
postulate
  playAnimation : ∀ {M Msg}
                → ModelHandle
                → String           -- Animation name
                → SceneNode M Msg  -- Model node
                → SceneNode M Msg

{-# COMPILE JS playAnimation = handle => animName => node => ({
  type: 'playAnimation',
  handle: handle,
  animationName: animName,
  child: node
}) #-}

-- Bind animation to model state
-- Extract animation parameters from model
record AnimationBinding : Set where
  constructor animBinding
  field
    animationName : String
    loop          : Bool
    speed         : Float

postulate
  bindAnimation : ∀ {M Msg}
                → ModelHandle
                → (M → AnimationBinding)
                → SceneNode M Msg
                → SceneNode M Msg

{-# COMPILE JS bindAnimation = handle => extract => node => ({
  type: 'bindAnimation',
  handle: handle,
  extract: extract,
  child: node
}) #-}

------------------------------------------------------------------------
-- Material overrides
------------------------------------------------------------------------

-- Override all materials in the model
postulate
  withMaterial : ∀ {M Msg}
               → Material
               → SceneNode M Msg
               → SceneNode M Msg

{-# COMPILE JS withMaterial = material => node => ({
  type: 'overrideMaterial',
  material: material,
  child: node
}) #-}

-- Override material for a specific mesh by name
postulate
  withMeshMaterial : ∀ {M Msg}
                   → String
                   → Material
                   → SceneNode M Msg
                   → SceneNode M Msg

{-# COMPILE JS withMeshMaterial = meshName => material => node => ({
  type: 'overrideMeshMaterial',
  meshName: meshName,
  material: material,
  child: node
}) #-}

------------------------------------------------------------------------
-- Model queries (compile-time, for generating code)
------------------------------------------------------------------------

-- These return lists of names that can be used with modelNode, meshGeometry, etc.
-- In practice, you'd inspect the model file and hard-code the names.

-- Placeholder: get list of mesh names in model
postulate
  getMeshNames : ModelHandle → List String

{-# COMPILE JS getMeshNames = handle => [] #-}  -- Runtime would populate

-- Placeholder: get list of animation names
postulate
  getAnimationNames : ModelHandle → List String

{-# COMPILE JS getAnimationNames = handle => [] #-}  -- Runtime would populate

------------------------------------------------------------------------
-- Convenience functions
------------------------------------------------------------------------

-- Load and display a model at origin
simpleModel : ∀ {M Msg} → String → SceneNode M Msg
simpleModel url = model (loadModel url) [] identityTransform

-- Load and display with transform
modelAt : ∀ {M Msg} → String → Transform → SceneNode M Msg
modelAt url transform = model (loadModel url) [] transform

-- Load and display with interactive attributes
interactiveModel : ∀ {M Msg} → String → List (SceneAttr Msg) → SceneNode M Msg
interactiveModel url attrs = model (loadModel url) attrs identityTransform
