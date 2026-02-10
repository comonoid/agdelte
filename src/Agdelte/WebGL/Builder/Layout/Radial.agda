{-# OPTIONS --without-K #-}

-- Layout.Radial: Circular and radial layouts for 3D scenes
--
-- Arranges children in circles, arcs, spirals, etc.

module Agdelte.WebGL.Builder.Layout.Radial where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Float as F using (Float)
open import Data.List using (List; []; _∷_; length)

open import Agdelte.WebGL.Types

------------------------------------------------------------------------
-- Math helpers (postulates for JS FFI)
------------------------------------------------------------------------

postulate
  sin : Float → Float
  cos : Float → Float
  π : Float
  _÷_ : Float → Float → Float

{-# COMPILE JS sin = Math.sin #-}
{-# COMPILE JS cos = Math.cos #-}
{-# COMPILE JS π = Math.PI #-}
{-# COMPILE JS _÷_ = a => b => a / b #-}

infixl 7 _÷_

private
  natToFloat : ℕ → Float
  natToFloat zero = 0.0
  natToFloat (suc n) = 1.0 F.+ natToFloat n

  -- Two pi
  τ : Float
  τ = 2.0 F.* π

------------------------------------------------------------------------
-- Ring layout (full circle in XZ plane)
------------------------------------------------------------------------

-- Arrange children in a circle (XZ plane, Y up)
ring3D : ∀ {M Msg}
       → Float            -- radius
       → List (SceneNode M Msg)
       → SceneNode M Msg
ring3D {M} {Msg} radius children =
  let n = length children
      angleStep = τ ÷ natToFloat n
  in group identityTransform (go 0 angleStep children)
  where
    go : ℕ → Float → List (SceneNode M Msg) → List (SceneNode M Msg)
    go _ _ [] = []
    go idx step (child ∷ rest) =
      let angle = natToFloat idx F.* step
          x = radius F.* cos angle
          z = radius F.* sin angle
          t = mkTransform (vec3 x 0.0 z) identityQuat (vec3 1.0 1.0 1.0)
      in bindTransform (λ _ → t) child ∷ go (suc idx) step rest

-- Ring with items facing center
ringFacing : ∀ {M Msg}
           → Float            -- radius
           → List (SceneNode M Msg)
           → SceneNode M Msg
ringFacing {M} {Msg} radius children =
  let n = length children
      angleStep = τ ÷ natToFloat n
  in group identityTransform (go 0 angleStep children)
  where
    halfAngle : Float → Float
    halfAngle a = a F.* 0.5

    go : ℕ → Float → List (SceneNode M Msg) → List (SceneNode M Msg)
    go _ _ [] = []
    go idx step (child ∷ rest) =
      let angle = natToFloat idx F.* step
          x = radius F.* cos angle
          z = radius F.* sin angle
          ha = halfAngle angle
          -- Rotation to face center (rotate around Y)
          rotY = quat 0.0 (sin ha) 0.0 (cos ha)
          t = mkTransform (vec3 x 0.0 z) rotY (vec3 1.0 1.0 1.0)
      in bindTransform (λ _ → t) child ∷ go (suc idx) step rest

------------------------------------------------------------------------
-- Arc layout (partial circle)
------------------------------------------------------------------------

-- Arrange children along an arc
arc3D : ∀ {M Msg}
      → Float            -- radius
      → Float            -- start angle (radians)
      → Float            -- end angle (radians)
      → List (SceneNode M Msg)
      → SceneNode M Msg
arc3D {M} {Msg} radius startAngle endAngle children =
  let n = length children
      arcLength = endAngle F.- startAngle
      angleStep = case n of λ where
                    zero → 0.0
                    (suc zero) → 0.0
                    (suc (suc _)) → arcLength ÷ natToFloat (pred n)
  in group identityTransform (go 0 startAngle angleStep children)
  where
    case_of_ : ∀ {A B : Set} → A → (A → B) → B
    case x of f = f x

    pred : ℕ → ℕ
    pred zero = zero
    pred (suc n) = n

    go : ℕ → Float → Float → List (SceneNode M Msg) → List (SceneNode M Msg)
    go _ _ _ [] = []
    go idx start step (child ∷ rest) =
      let angle = start F.+ (natToFloat idx F.* step)
          x = radius F.* cos angle
          z = radius F.* sin angle
          t = mkTransform (vec3 x 0.0 z) identityQuat (vec3 1.0 1.0 1.0)
      in bindTransform (λ _ → t) child ∷ go (suc idx) start step rest

------------------------------------------------------------------------
-- Spiral layout
------------------------------------------------------------------------

-- Arrange children in a spiral (XZ plane)
spiral3D : ∀ {M Msg}
         → Float            -- start radius
         → Float            -- end radius
         → Float            -- total angle (radians, e.g. 4π for 2 turns)
         → List (SceneNode M Msg)
         → SceneNode M Msg
spiral3D {M} {Msg} startRadius endRadius totalAngle children =
  let n = length children
      angleStep = totalAngle ÷ natToFloat n
      radiusStep = (endRadius F.- startRadius) ÷ natToFloat n
  in group identityTransform (go 0 0.0 startRadius angleStep radiusStep children)
  where
    go : ℕ → Float → Float → Float → Float → List (SceneNode M Msg) → List (SceneNode M Msg)
    go _ _ _ _ _ [] = []
    go idx angle radius aStep rStep (child ∷ rest) =
      let x = radius F.* cos angle
          z = radius F.* sin angle
          t = mkTransform (vec3 x 0.0 z) identityQuat (vec3 1.0 1.0 1.0)
      in bindTransform (λ _ → t) child
         ∷ go (suc idx) (angle F.+ aStep) (radius F.+ rStep) aStep rStep rest
