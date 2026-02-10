{-# OPTIONS --without-K #-}

-- Geometry.Procedural: Procedural geometry generation
--
-- Provides functions to create geometry from paths and profiles:
-- extrusion, revolution, lofting, and sweeping.

module Agdelte.WebGL.Builder.Geometry.Procedural where

open import Data.Nat using (ℕ)
open import Data.Float using (Float)
open import Data.List using (List)
open import Data.Bool using (Bool; true; false)

open import Agdelte.WebGL.Types

------------------------------------------------------------------------
-- Path and Profile types
------------------------------------------------------------------------

-- A 2D point for profiles
record Point2D : Set where
  constructor point2d
  field
    x y : Float

-- A 2D path (list of points)
Path2D : Set
Path2D = List Point2D

-- A 3D path for sweeping
Path3D : Set
Path3D = List Vec3

------------------------------------------------------------------------
-- Extrusion
------------------------------------------------------------------------

-- Extrude a 2D profile along the Z axis
-- profile: 2D shape to extrude
-- depth: extrusion depth
-- segments: number of segments along depth
-- caps: whether to add end caps
postulate
  extrude : Path2D → Float → ℕ → Bool → Geometry

{-# COMPILE JS extrude = profile => depth => segments => caps => ({
  type: 'extrude',
  profile: profile,
  depth: depth,
  segments: Number(segments),
  caps: caps
}) #-}

-- Extrude with scale: taper the extrusion
postulate
  extrudeScaled : Path2D → Float → Float → Float → ℕ → Geometry

{-# COMPILE JS extrudeScaled = profile => depth => startScale => endScale => segments => ({
  type: 'extrudeScaled',
  profile: profile,
  depth: depth,
  startScale: startScale,
  endScale: endScale,
  segments: Number(segments)
}) #-}

-- Extrude with twist: rotate along extrusion
postulate
  extrudeTwist : Path2D → Float → Float → ℕ → Geometry

{-# COMPILE JS extrudeTwist = profile => depth => twistAngle => segments => ({
  type: 'extrudeTwist',
  profile: profile,
  depth: depth,
  twistAngle: twistAngle,
  segments: Number(segments)
}) #-}

------------------------------------------------------------------------
-- Revolution (Lathe)
------------------------------------------------------------------------

-- Revolve a 2D profile around the Y axis
-- profile: 2D shape to revolve (x = radius, y = height)
-- angle: revolution angle in radians (2π for full revolution)
-- segments: number of radial segments
postulate
  revolve : Path2D → Float → ℕ → Geometry

{-# COMPILE JS revolve = profile => angle => segments => ({
  type: 'revolve',
  profile: profile,
  angle: angle,
  segments: Number(segments)
}) #-}

-- Full 360-degree revolution
revolve360 : Path2D → ℕ → Geometry
revolve360 profile segments = revolve profile 6.283185307 segments

------------------------------------------------------------------------
-- Lofting
------------------------------------------------------------------------

-- Loft between multiple profiles
-- Creates smooth surface transitioning between profiles
postulate
  loft : List Path2D → ℕ → Geometry

{-# COMPILE JS loft = profiles => segments => ({
  type: 'loft',
  profiles: profiles,
  segments: Number(segments)
}) #-}

-- Loft with spine: profiles placed along a 3D path
postulate
  loftWithSpine : List Path2D → Path3D → ℕ → Geometry

{-# COMPILE JS loftWithSpine = profiles => spine => segments => ({
  type: 'loftWithSpine',
  profiles: profiles,
  spine: spine,
  segments: Number(segments)
}) #-}

------------------------------------------------------------------------
-- Sweeping
------------------------------------------------------------------------

-- Sweep a 2D profile along a 3D path
postulate
  sweep : Path2D → Path3D → ℕ → Geometry

{-# COMPILE JS sweep = profile => path => segments => ({
  type: 'sweep',
  profile: profile,
  path: path,
  segments: Number(segments)
}) #-}

-- Sweep with scaling along path
postulate
  sweepScaled : Path2D → Path3D → List Float → ℕ → Geometry

{-# COMPILE JS sweepScaled = profile => path => scales => segments => ({
  type: 'sweepScaled',
  profile: profile,
  path: path,
  scales: scales,
  segments: Number(segments)
}) #-}

------------------------------------------------------------------------
-- Profile constructors
------------------------------------------------------------------------

-- Create a circle profile
postulate
  circleProfile : Float → ℕ → Path2D

{-# COMPILE JS circleProfile = radius => segments => {
  const points = [];
  for (let i = 0; i <= segments; i++) {
    const angle = (i / segments) * 2 * Math.PI;
    points.push({ x: radius * Math.cos(angle), y: radius * Math.sin(angle) });
  }
  return points;
} #-}

-- Create a rectangle profile
postulate
  rectProfile : Float → Float → Path2D

{-# COMPILE JS rectProfile = width => height => {
  const hw = width / 2, hh = height / 2;
  return [
    { x: -hw, y: -hh },
    { x:  hw, y: -hh },
    { x:  hw, y:  hh },
    { x: -hw, y:  hh },
    { x: -hw, y: -hh }
  ];
} #-}

-- Create a rounded rectangle profile
postulate
  roundedRectProfile : Float → Float → Float → ℕ → Path2D

{-# COMPILE JS roundedRectProfile = width => height => radius => cornerSegments => {
  const points = [];
  const hw = width / 2 - radius;
  const hh = height / 2 - radius;

  // Generate corners
  const corners = [
    { cx: hw, cy: hh, start: 0 },
    { cx: -hw, cy: hh, start: Math.PI / 2 },
    { cx: -hw, cy: -hh, start: Math.PI },
    { cx: hw, cy: -hh, start: 3 * Math.PI / 2 }
  ];

  for (const corner of corners) {
    for (let i = 0; i <= cornerSegments; i++) {
      const angle = corner.start + (i / cornerSegments) * (Math.PI / 2);
      points.push({
        x: corner.cx + radius * Math.cos(angle),
        y: corner.cy + radius * Math.sin(angle)
      });
    }
  }

  // Close the path
  points.push(points[0]);
  return points;
} #-}

------------------------------------------------------------------------
-- Path constructors
------------------------------------------------------------------------

-- Create a straight line path
postulate
  linePath : Vec3 → Vec3 → ℕ → Path3D

{-# COMPILE JS linePath = start => end => segments => {
  const points = [];
  for (let i = 0; i <= segments; i++) {
    const t = i / segments;
    points.push({
      x: start.x + (end.x - start.x) * t,
      y: start.y + (end.y - start.y) * t,
      z: start.z + (end.z - start.z) * t
    });
  }
  return points;
} #-}

-- Create a helix path
postulate
  helixPath : Float → Float → Float → ℕ → Path3D

{-# COMPILE JS helixPath = radius => height => turns => segments => {
  const points = [];
  for (let i = 0; i <= segments; i++) {
    const t = i / segments;
    const angle = t * turns * 2 * Math.PI;
    points.push({
      x: radius * Math.cos(angle),
      y: t * height,
      z: radius * Math.sin(angle)
    });
  }
  return points;
} #-}

-- Create a Bezier curve path
postulate
  bezierPath : Vec3 → Vec3 → Vec3 → Vec3 → ℕ → Path3D

{-# COMPILE JS bezierPath = p0 => p1 => p2 => p3 => segments => {
  const points = [];
  for (let i = 0; i <= segments; i++) {
    const t = i / segments;
    const mt = 1 - t;
    const mt2 = mt * mt, mt3 = mt2 * mt;
    const t2 = t * t, t3 = t2 * t;
    points.push({
      x: mt3 * p0.x + 3 * mt2 * t * p1.x + 3 * mt * t2 * p2.x + t3 * p3.x,
      y: mt3 * p0.y + 3 * mt2 * t * p1.y + 3 * mt * t2 * p2.y + t3 * p3.y,
      z: mt3 * p0.z + 3 * mt2 * t * p1.z + 3 * mt * t2 * p2.z + t3 * p3.z
    });
  }
  return points;
} #-}
