{-# OPTIONS --without-K #-}

-- Shared math helpers for SVG controls
-- Extracted from Controls/Gauge, Controls/Knob, Charts/*, etc.

module Agdelte.Svg.Math where

open import Data.Float using (Float; _+_; _-_; _*_)
open import Data.Float.Base using (_÷_; _≤ᵇ_; _<ᵇ_)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (if_then_else_)
open import Data.Nat using (ℕ; zero; suc)

------------------------------------------------------------------------
-- Constants
------------------------------------------------------------------------

π : Float
π = 3.14159265359

------------------------------------------------------------------------
-- Angle helpers
------------------------------------------------------------------------

-- Normalize angle to [-π, π] by repeated subtraction/addition of 2π
normalize : Float → Float
normalize x = go x 20
  where
    twoPi : Float
    twoPi = 2.0 * π
    go : Float → ℕ → Float
    go y zero = y
    go y (suc n) = if π ≤ᵇ y       then go (y - twoPi) n
                   else if y ≤ᵇ (0.0 - π) then go (y + twoPi) n
                   else y

degToRad : Float → Float
degToRad d = d * π ÷ 180.0

------------------------------------------------------------------------
-- Trig approximations (Taylor series with range reduction)
------------------------------------------------------------------------

sin : Float → Float
sin x' = let x = normalize x'
          in x - (x * x * x ÷ 6.0)
           + (x * x * x * x * x ÷ 120.0)
           - (x * x * x * x * x * x * x ÷ 5040.0)

cos : Float → Float
cos x' = let x = normalize x'
          in 1.0 - (x * x ÷ 2.0)
           + (x * x * x * x ÷ 24.0)
           - (x * x * x * x * x * x ÷ 720.0)

------------------------------------------------------------------------
-- Clamping
------------------------------------------------------------------------

clamp : Float → Float → Float → Float
clamp lo hi v = if v ≤ᵇ lo then lo else if hi ≤ᵇ v then hi else v

clamp01 : Float → Float
clamp01 = clamp 0.0 1.0

------------------------------------------------------------------------
-- List min/max
------------------------------------------------------------------------

findMin : List Float → Float → Float
findMin [] acc = acc
findMin (v ∷ vs) acc = findMin vs (if v <ᵇ acc then v else acc)

findMax : List Float → Float → Float
findMax [] acc = acc
findMax (v ∷ vs) acc = findMax vs (if acc <ᵇ v then v else acc)

-- Last element of a list (default 0.0)
getLast : List Float → Float
getLast [] = 0.0
getLast (v ∷ []) = v
getLast (_ ∷ vs) = getLast vs

-- Zero-anchoring: ensure range always includes zero
zeroMin : Float → Float
zeroMin v = if v <ᵇ 0.0 then v else 0.0

zeroMax : Float → Float
zeroMax v = if 0.0 <ᵇ v then v else 0.0
