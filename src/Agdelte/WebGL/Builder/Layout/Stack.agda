{-# OPTIONS --without-K #-}

-- Layout.Stack: Linear layouts for 3D scenes
--
-- Arranges children along an axis with specified spacing.
-- Each child is placed at a fixed offset from the previous one.

module Agdelte.WebGL.Builder.Layout.Stack where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Float as F using (Float)
open import Data.List using (List; []; _∷_; length)

open import Agdelte.WebGL.Types

------------------------------------------------------------------------
-- Axis specification
------------------------------------------------------------------------

data Axis : Set where
  X Y Z : Axis

------------------------------------------------------------------------
-- Private helpers
------------------------------------------------------------------------

private
  -- Apply offset along axis to transform
  offsetTransform : Axis → Float → Transform → Transform
  offsetTransform X offset (mkTransform pos rot scale) =
    mkTransform (vec3 (vec3X pos F.+ offset) (vec3Y pos) (vec3Z pos)) rot scale
  offsetTransform Y offset (mkTransform pos rot scale) =
    mkTransform (vec3 (vec3X pos) (vec3Y pos F.+ offset) (vec3Z pos)) rot scale
  offsetTransform Z offset (mkTransform pos rot scale) =
    mkTransform (vec3 (vec3X pos) (vec3Y pos) (vec3Z pos F.+ offset)) rot scale

  natToFloat : ℕ → Float
  natToFloat zero = 0.0
  natToFloat (suc n) = 1.0 F.+ natToFloat n

  monus : ℕ → ℕ → ℕ
  monus zero _ = zero
  monus (suc m) zero = suc m
  monus (suc m) (suc k) = monus m k

------------------------------------------------------------------------
-- Stack layouts
------------------------------------------------------------------------

-- Stack along X axis (horizontal)
hstack3D : ∀ {M Msg} → Float → List (SceneNode M Msg) → SceneNode M Msg
hstack3D {M} {Msg} spacing children = group identityTransform (go 0.0 children)
  where
    go : Float → List (SceneNode M Msg) → List (SceneNode M Msg)
    go _ [] = []
    go pos (child ∷ rest) =
      bindTransform (λ _ → offsetTransform X pos identityTransform) child
      ∷ go (pos F.+ spacing) rest

-- Stack along Y axis (vertical)
vstack3D : ∀ {M Msg} → Float → List (SceneNode M Msg) → SceneNode M Msg
vstack3D {M} {Msg} spacing children = group identityTransform (go 0.0 children)
  where
    go : Float → List (SceneNode M Msg) → List (SceneNode M Msg)
    go _ [] = []
    go pos (child ∷ rest) =
      bindTransform (λ _ → offsetTransform Y pos identityTransform) child
      ∷ go (pos F.+ spacing) rest

-- Stack along Z axis (depth)
dstack3D : ∀ {M Msg} → Float → List (SceneNode M Msg) → SceneNode M Msg
dstack3D {M} {Msg} spacing children = group identityTransform (go 0.0 children)
  where
    go : Float → List (SceneNode M Msg) → List (SceneNode M Msg)
    go _ [] = []
    go pos (child ∷ rest) =
      bindTransform (λ _ → offsetTransform Z pos identityTransform) child
      ∷ go (pos F.+ spacing) rest

-- Generic stack along any axis
stack3D : ∀ {M Msg} → Axis → Float → List (SceneNode M Msg) → SceneNode M Msg
stack3D X = hstack3D
stack3D Y = vstack3D
stack3D Z = dstack3D

------------------------------------------------------------------------
-- Centered stacks (children centered around origin)
------------------------------------------------------------------------

private
  -- Center offset for n items with spacing
  -- Returns negative half of total span
  centerOffset : ℕ → Float → Float
  centerOffset n spacing =
    neg (spacing F.* natToFloat (monus n 1)) F.* 0.5
    where
      neg : Float → Float
      neg x = 0.0 F.- x

-- Centered horizontal stack
hstackCentered : ∀ {M Msg} → Float → List (SceneNode M Msg) → SceneNode M Msg
hstackCentered {M} {Msg} spacing children =
  let n = length children
      offset = centerOffset n spacing
  in group identityTransform (go offset children)
  where
    go : Float → List (SceneNode M Msg) → List (SceneNode M Msg)
    go _ [] = []
    go pos (child ∷ rest) =
      bindTransform (λ _ → offsetTransform X pos identityTransform) child
      ∷ go (pos F.+ spacing) rest

-- Centered vertical stack
vstackCentered : ∀ {M Msg} → Float → List (SceneNode M Msg) → SceneNode M Msg
vstackCentered {M} {Msg} spacing children =
  let n = length children
      offset = centerOffset n spacing
  in group identityTransform (go offset children)
  where
    go : Float → List (SceneNode M Msg) → List (SceneNode M Msg)
    go _ [] = []
    go pos (child ∷ rest) =
      bindTransform (λ _ → offsetTransform Y pos identityTransform) child
      ∷ go (pos F.+ spacing) rest

-- Centered depth stack
dstackCentered : ∀ {M Msg} → Float → List (SceneNode M Msg) → SceneNode M Msg
dstackCentered {M} {Msg} spacing children =
  let n = length children
      offset = centerOffset n spacing
  in group identityTransform (go offset children)
  where
    go : Float → List (SceneNode M Msg) → List (SceneNode M Msg)
    go _ [] = []
    go pos (child ∷ rest) =
      bindTransform (λ _ → offsetTransform Z pos identityTransform) child
      ∷ go (pos F.+ spacing) rest
