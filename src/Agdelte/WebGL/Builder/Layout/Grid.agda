{-# OPTIONS --without-K #-}

-- Layout.Grid: 2D grid layouts for 3D scenes
--
-- Arranges children in a grid pattern in a specified plane.

module Agdelte.WebGL.Builder.Layout.Grid where

open import Data.Nat using (ℕ; zero; suc; _*_; _+_)
open import Data.Float as F using (Float)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_×_; _,_)

open import Agdelte.WebGL.Types

------------------------------------------------------------------------
-- Plane specification
------------------------------------------------------------------------

data Plane : Set where
  XY XZ YZ : Plane

------------------------------------------------------------------------
-- Private helpers
------------------------------------------------------------------------

private
  natToFloat : ℕ → Float
  natToFloat zero = 0.0
  natToFloat (suc n) = 1.0 F.+ natToFloat n

  -- Transform for grid cell in plane
  gridTransform : Plane → Float → Float → ℕ → ℕ → Transform
  gridTransform XY spacingX spacingY col row =
    mkTransform
      (vec3 (natToFloat col F.* spacingX) (natToFloat row F.* spacingY) 0.0)
      identityQuat
      (vec3 1.0 1.0 1.0)
  gridTransform XZ spacingX spacingZ col row =
    mkTransform
      (vec3 (natToFloat col F.* spacingX) 0.0 (natToFloat row F.* spacingZ))
      identityQuat
      (vec3 1.0 1.0 1.0)
  gridTransform YZ spacingY spacingZ col row =
    mkTransform
      (vec3 0.0 (natToFloat col F.* spacingY) (natToFloat row F.* spacingZ))
      identityQuat
      (vec3 1.0 1.0 1.0)

------------------------------------------------------------------------
-- Grid layout (using postulates for div/mod to avoid termination issues)
------------------------------------------------------------------------

postulate
  divNat : ℕ → ℕ → ℕ
  modNat : ℕ → ℕ → ℕ

{-# COMPILE JS divNat = n => d => d === 0n ? 0n : n / d #-}
{-# COMPILE JS modNat = n => d => d === 0n ? 0n : n % d #-}

-- Simple grid with automatic row wrapping
gridAuto : ∀ {M Msg}
         → ℕ              -- columns (rows determined by item count)
         → Float          -- cell spacing
         → Plane          -- which plane
         → List (SceneNode M Msg)
         → SceneNode M Msg
gridAuto {M} {Msg} cols spacing pl children =
  group identityTransform (go 0 children)
  where
    cols' : ℕ
    cols' = suc (case cols of λ { zero → zero ; (suc n) → n })
      where
        case_of_ : ∀ {A B : Set} → A → (A → B) → B
        case x of f = f x

    go : ℕ → List (SceneNode M Msg) → List (SceneNode M Msg)
    go _ [] = []
    go idx (child ∷ rest) =
      let col = modNat idx cols'
          row = divNat idx cols'
      in bindTransform (λ _ → gridTransform pl spacing spacing col row) child
         ∷ go (suc idx) rest

-- Grid with specified dimensions (cols × rows)
grid : ∀ {M Msg}
     → ℕ × ℕ           -- columns × rows
     → Float × Float   -- spacing (x, y in plane)
     → Plane           -- which plane
     → List (SceneNode M Msg)
     → SceneNode M Msg
grid {M} {Msg} (cols , _) (spX , spY) pl children =
  group identityTransform (go 0 children)
  where
    cols' : ℕ
    cols' = suc (case cols of λ { zero → zero ; (suc n) → n })
      where
        case_of_ : ∀ {A B : Set} → A → (A → B) → B
        case x of f = f x

    go : ℕ → List (SceneNode M Msg) → List (SceneNode M Msg)
    go _ [] = []
    go idx (child ∷ rest) =
      let col = modNat idx cols'
          row = divNat idx cols'
      in bindTransform (λ _ → gridTransform pl spX spY col row) child
         ∷ go (suc idx) rest
