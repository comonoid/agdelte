{-# OPTIONS --without-K #-}

-- Geometry.Primitives: Additional parametric primitives
--
-- Extends the basic primitives in Types with more complex shapes.
-- All primitives compile to JS functions that generate vertex data.

module Agdelte.WebGL.Builder.Geometry.Primitives where

open import Data.Nat using (ℕ)
open import Data.Float using (Float)

open import Agdelte.WebGL.Types

------------------------------------------------------------------------
-- Additional primitives (FFI to JS geometry generators)
------------------------------------------------------------------------

postulate
  -- Rounded box: box with rounded edges
  -- dims: width, height, depth
  -- radius: corner radius
  -- segments: smoothness of corners
  roundedBox : Vec3 → Float → ℕ → Geometry

  -- Capsule: cylinder with hemispherical caps
  -- radius: radius of cylinder and caps
  -- height: total height including caps
  -- segments: radial segments
  capsule : Float → Float → ℕ → Geometry

  -- Torus: donut shape
  -- majorRadius: distance from center to tube center
  -- minorRadius: tube radius
  -- majorSegments: segments around the ring
  -- minorSegments: segments around the tube
  torus : Float → Float → ℕ → ℕ → Geometry

  -- Cone: tapered cylinder
  -- bottomRadius: radius at base
  -- topRadius: radius at top (0 for point)
  -- height: height of cone
  -- segments: radial segments
  cone : Float → Float → Float → ℕ → Geometry

  -- Pyramid: n-sided pyramid
  -- baseSize: size of base
  -- height: height of pyramid
  -- sides: number of sides (3 = triangular, 4 = square, etc.)
  pyramid : Float → Float → ℕ → Geometry

  -- Tube: hollow cylinder (pipe)
  -- innerRadius: inner radius
  -- outerRadius: outer radius
  -- height: height of tube
  -- segments: radial segments
  tube : Float → Float → Float → ℕ → Geometry

  -- Ring (flat): 2D ring/washer shape
  -- innerRadius: hole radius
  -- outerRadius: outer radius
  -- segments: radial segments
  ring : Float → Float → ℕ → Geometry

  -- Icosahedron: 20-sided polyhedron
  -- radius: circumscribed sphere radius
  icosahedron : Float → Geometry

  -- Dodecahedron: 12-sided polyhedron
  -- radius: circumscribed sphere radius
  dodecahedron : Float → Geometry

  -- Octahedron: 8-sided polyhedron (two pyramids base-to-base)
  -- radius: circumscribed sphere radius
  octahedron : Float → Geometry

  -- Tetrahedron: 4-sided polyhedron
  -- radius: circumscribed sphere radius
  tetrahedron : Float → Geometry

------------------------------------------------------------------------
-- JS FFI bindings
------------------------------------------------------------------------

{-# COMPILE JS roundedBox = dims => radius => segments => ({
  type: 'roundedBox',
  dims: dims,
  radius: radius,
  segments: Number(segments)
}) #-}

{-# COMPILE JS capsule = radius => height => segments => ({
  type: 'capsule',
  radius: radius,
  height: height,
  segments: Number(segments)
}) #-}

{-# COMPILE JS torus = majorR => minorR => majorSeg => minorSeg => ({
  type: 'torus',
  majorRadius: majorR,
  minorRadius: minorR,
  majorSegments: Number(majorSeg),
  minorSegments: Number(minorSeg)
}) #-}

{-# COMPILE JS cone = bottomR => topR => height => segments => ({
  type: 'cone',
  bottomRadius: bottomR,
  topRadius: topR,
  height: height,
  segments: Number(segments)
}) #-}

{-# COMPILE JS pyramid = baseSize => height => sides => ({
  type: 'pyramid',
  baseSize: baseSize,
  height: height,
  sides: Number(sides)
}) #-}

{-# COMPILE JS tube = innerR => outerR => height => segments => ({
  type: 'tube',
  innerRadius: innerR,
  outerRadius: outerR,
  height: height,
  segments: Number(segments)
}) #-}

{-# COMPILE JS ring = innerR => outerR => segments => ({
  type: 'ring',
  innerRadius: innerR,
  outerRadius: outerR,
  segments: Number(segments)
}) #-}

{-# COMPILE JS icosahedron = radius => ({
  type: 'icosahedron',
  radius: radius
}) #-}

{-# COMPILE JS dodecahedron = radius => ({
  type: 'dodecahedron',
  radius: radius
}) #-}

{-# COMPILE JS octahedron = radius => ({
  type: 'octahedron',
  radius: radius
}) #-}

{-# COMPILE JS tetrahedron = radius => ({
  type: 'tetrahedron',
  radius: radius
}) #-}

------------------------------------------------------------------------
-- Convenience functions with default segments
------------------------------------------------------------------------

-- Rounded box with default smoothness
roundedBox' : Vec3 → Float → Geometry
roundedBox' dims radius = roundedBox dims radius 4

-- Capsule with default segments
capsule' : Float → Float → Geometry
capsule' radius height = capsule radius height 16

-- Torus with default segments
torus' : Float → Float → Geometry
torus' majorR minorR = torus majorR minorR 24 12

-- Cone with default segments (pointed)
cone' : Float → Float → Geometry
cone' radius height = cone radius 0.0 height 24

-- Square pyramid
pyramidSquare : Float → Float → Geometry
pyramidSquare baseSize height = pyramid baseSize height 4

-- Triangular pyramid (tetrahedron-like but with specified dimensions)
pyramidTriangular : Float → Float → Geometry
pyramidTriangular baseSize height = pyramid baseSize height 3
