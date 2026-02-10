{-# OPTIONS --without-K #-}

-- Geometry.CSG: Constructive Solid Geometry operations
--
-- Provides boolean operations on 3D geometry:
-- union, subtraction, and intersection.

module Agdelte.WebGL.Builder.Geometry.CSG where

open import Data.List using (List; []; _∷_)
open import Data.Float using (Float)

open import Agdelte.WebGL.Types

------------------------------------------------------------------------
-- Basic CSG operations
------------------------------------------------------------------------

-- Union: combine two geometries into one
-- Result contains all points inside either geometry
postulate
  union : Geometry → Geometry → Geometry

{-# COMPILE JS union = a => b => ({
  type: 'csgUnion',
  operandA: a,
  operandB: b
}) #-}

-- Subtract: remove geometry B from geometry A
-- Result contains points in A but not in B
postulate
  subtract : Geometry → Geometry → Geometry

{-# COMPILE JS subtract = a => b => ({
  type: 'csgSubtract',
  operandA: a,
  operandB: b
}) #-}

-- Intersect: keep only overlapping volume
-- Result contains points inside both A and B
postulate
  intersect : Geometry → Geometry → Geometry

{-# COMPILE JS intersect = a => b => ({
  type: 'csgIntersect',
  operandA: a,
  operandB: b
}) #-}

------------------------------------------------------------------------
-- Convenience operators
------------------------------------------------------------------------

-- Infix union
_∪_ : Geometry → Geometry → Geometry
_∪_ = union

-- Infix subtraction
_∖_ : Geometry → Geometry → Geometry
_∖_ = subtract

-- Infix intersection
_∩_ : Geometry → Geometry → Geometry
_∩_ = intersect

infixl 6 _∪_
infixl 7 _∩_
infixl 7 _∖_

------------------------------------------------------------------------
-- Multi-operand operations
------------------------------------------------------------------------

-- Union of multiple geometries
unionAll : List Geometry → Geometry
unionAll [] = box (vec3 0.0 0.0 0.0)
unionAll (g ∷ []) = g
unionAll (g ∷ gs) = union g (unionAll gs)

-- Subtract multiple geometries from one
subtractAll : Geometry → List Geometry → Geometry
subtractAll base [] = base
subtractAll base (g ∷ gs) = subtractAll (subtract base g) gs

-- Intersect multiple geometries
intersectAll : List Geometry → Geometry
intersectAll [] = box (vec3 0.0 0.0 0.0)
intersectAll (g ∷ []) = g
intersectAll (g ∷ gs) = intersect g (intersectAll gs)

------------------------------------------------------------------------
-- CSG with transforms
------------------------------------------------------------------------

-- CSG operation with transformed operand
-- Apply transform to B before operation
postulate
  unionTransformed : Geometry → Geometry → Transform → Geometry

{-# COMPILE JS unionTransformed = a => b => transform => ({
  type: 'csgUnion',
  operandA: a,
  operandB: b,
  transformB: transform
}) #-}

postulate
  subtractTransformed : Geometry → Geometry → Transform → Geometry

{-# COMPILE JS subtractTransformed = a => b => transform => ({
  type: 'csgSubtract',
  operandA: a,
  operandB: b,
  transformB: transform
}) #-}

postulate
  intersectTransformed : Geometry → Geometry → Transform → Geometry

{-# COMPILE JS intersectTransformed = a => b => transform => ({
  type: 'csgIntersect',
  operandA: a,
  operandB: b,
  transformB: transform
}) #-}

------------------------------------------------------------------------
-- Hollow operations
------------------------------------------------------------------------

-- Create a hollow version of a geometry (shell)
-- thickness: wall thickness
postulate
  hollow : Geometry → Float → Geometry

{-# COMPILE JS hollow = geom => thickness => ({
  type: 'csgHollow',
  operand: geom,
  thickness: thickness
}) #-}

-- Create a shell with one face open
postulate
  openHollow : Geometry → Float → Vec3 → Geometry

{-# COMPILE JS openHollow = geom => thickness => openDirection => ({
  type: 'csgOpenHollow',
  operand: geom,
  thickness: thickness,
  openDirection: openDirection
}) #-}

------------------------------------------------------------------------
-- Edge operations
------------------------------------------------------------------------

-- Round (fillet) all edges of a geometry
postulate
  fillet : Geometry → Float → Geometry

{-# COMPILE JS fillet = geom => radius => ({
  type: 'csgFillet',
  operand: geom,
  radius: radius
}) #-}

-- Chamfer (bevel) all edges of a geometry
postulate
  chamfer : Geometry → Float → Geometry

{-# COMPILE JS chamfer = geom => size => ({
  type: 'csgChamfer',
  operand: geom,
  size: size
}) #-}
