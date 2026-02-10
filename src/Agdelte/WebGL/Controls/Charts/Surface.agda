{-# OPTIONS --without-K #-}

-- WebGL Controls Charts Surface
--
-- 3D surface plots for visualizing height fields and functions.
-- Supports solid surfaces, wireframes, and contour plots.

module Agdelte.WebGL.Controls.Charts.Surface where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Float using (Float; _*_; _+_; _-_; -_)
open import Data.String using (String)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false; if_then_else_)

open import Agdelte.WebGL.Types
open import Agdelte.WebGL.Builder.Geometry.Primitives
open import Agdelte.WebGL.Controls.Theme

------------------------------------------------------------------------
-- Helper postulates
------------------------------------------------------------------------

postulate
  natToFloat : ℕ → Float
  sinF : Float → Float
  cosF : Float → Float
  absFloat : Float → Float
  _<F_ : Float → Float → Bool
  _>F_ : Float → Float → Bool

{-# COMPILE JS natToFloat = n => Number(n) #-}
{-# COMPILE JS sinF = x => Math.sin(x) #-}
{-# COMPILE JS cosF = x => Math.cos(x) #-}
{-# COMPILE JS absFloat = x => Math.abs(x) #-}
{-# COMPILE JS _<F_ = x => y => x < y #-}
{-# COMPILE JS _>F_ = x => y => x > y #-}

------------------------------------------------------------------------
-- Surface configuration
------------------------------------------------------------------------

record SurfaceConfig : Set where
  constructor mkSurfaceConfig
  field
    resolutionX : ℕ              -- Grid resolution in X
    resolutionZ : ℕ              -- Grid resolution in Z
    bounds      : Vec3           -- Size (width, maxHeight, depth)
    wireframe   : Bool           -- Render as wireframe
    showBase    : Bool           -- Show base plane

defaultSurfaceConfig : SurfaceConfig
defaultSurfaceConfig = mkSurfaceConfig
  20                              -- resolutionX
  20                              -- resolutionZ
  (vec3 1.0 0.5 1.0)             -- bounds
  false                           -- wireframe
  true                            -- showBase

wireframeSurfaceConfig : SurfaceConfig
wireframeSurfaceConfig = mkSurfaceConfig
  15                              -- resolutionX
  15                              -- resolutionZ
  (vec3 1.0 0.5 1.0)             -- bounds
  true                            -- wireframe
  false                           -- showBase

------------------------------------------------------------------------
-- Color mapping
------------------------------------------------------------------------

-- Height to color function type
HeightColorMap : Set
HeightColorMap = Float → GlColor

-- Default color maps
heatMap : HeightColorMap
heatMap h =
  let t = h * 4.0  -- Expand range for more gradient
      r = if t <F 1.0 then 0.0 else if t <F 2.0 then t - 1.0 else 1.0
      g = if t <F 1.0 then t else if t <F 3.0 then 1.0 else 4.0 - t
      b = if t <F 2.0 then 1.0 - t * 0.5 else 0.0
  in rgba (clamp01 r) (clamp01 g) (clamp01 b) 1.0
  where
    clamp01 : Float → Float
    clamp01 x = if x <F 0.0 then 0.0 else if x >F 1.0 then 1.0 else x

coolWarmMap : HeightColorMap
coolWarmMap h =
  let t = h
      r = 0.3 + t * 0.7
      g = 0.3 + (1.0 - absFloat (t - 0.5) * 2.0) * 0.4
      b = 0.9 - t * 0.6
  in rgba r g b 1.0

terrainMap : HeightColorMap
terrainMap h =
  -- Blue (water) -> Green (land) -> Brown (mountains) -> White (snow)
  let t = h
  in if t <F 0.2 then rgba 0.1 0.3 0.8 1.0          -- water
     else if t <F 0.4 then rgba 0.2 0.6 0.2 1.0     -- lowland
     else if t <F 0.7 then rgba 0.5 0.4 0.2 1.0     -- mountain
     else rgba 0.95 0.95 0.95 1.0                   -- snow

------------------------------------------------------------------------
-- Helper: list append
------------------------------------------------------------------------

infixr 5 _++L_
_++L_ : ∀ {A : Set} → List A → List A → List A
[] ++L ys = ys
(x ∷ xs) ++L ys = x ∷ (xs ++L ys)

------------------------------------------------------------------------
-- Surface plot implementation
------------------------------------------------------------------------

-- Height function type: (x, z) → height
HeightFunction : Set → Set
HeightFunction M = M → Float → Float → Float

-- 3D surface plot
surfacePlot3D : ∀ {M Msg}
              → ControlTheme
              → SurfaceConfig
              → HeightFunction M             -- Height function
              → HeightColorMap               -- Color mapping
              → Transform
              → SceneNode M Msg
surfacePlot3D {M} {Msg} theme config getHeight colorMap t =
  let resX = SurfaceConfig.resolutionX config
      resZ = SurfaceConfig.resolutionZ config
      bounds = SurfaceConfig.bounds config
      width = vec3X bounds
      maxH = vec3Y bounds
      depth = vec3Z bounds
      wire = SurfaceConfig.wireframe config
      showB = SurfaceConfig.showBase config
  in group t
       ( (if showB then basePlane width depth ∷ [] else [])
       ++L bindChildren (buildSurface resX resZ width maxH depth wire colorMap getHeight)
            identityTransform
       ∷ [])
  where

    -- Base plane
    basePlane : Float → Float → SceneNode M Msg
    basePlane w d =
      let baseGeom = roundedBox (vec3 w 0.01 d) 0.005 4
          baseMat = phong (rgba 0.2 0.2 0.2 0.5) 16.0
      in mesh baseGeom baseMat [] identityTransform

    -- Build surface as grid of small boxes
    buildSurface : ℕ → ℕ → Float → Float → Float → Bool → HeightColorMap
                 → HeightFunction M → M → List (SceneNode M Msg)
    buildSurface resX resZ w maxH d wire cmap heightFn m =
      let stepX = w * recip (natToFloat resX)
          stepZ = d * recip (natToFloat resZ)
          startX = - (w * 0.5) + stepX * 0.5
          startZ = - (d * 0.5) + stepZ * 0.5
      in buildRows startX startZ stepX stepZ maxH wire cmap heightFn m 0 resZ
      where
        postulate recip : Float → Float
        {-# COMPILE JS recip = x => 1 / x #-}

        buildRow : Float → Float → Float → Float → Float → Bool → HeightColorMap
                 → HeightFunction M → M → ℕ → ℕ → List (SceneNode M Msg)
        buildRow _ _ _ _ _ _ _ _ _ _ zero = []
        buildRow startX z stepX stepZ maxH wire cmap heightFn m xIdx (suc remaining) =
          let x = startX + natToFloat xIdx * stepX
              -- Get height value (normalized 0-1)
              h = heightFn m x z
              -- Clamp height
              hClamped = if h <F 0.0 then 0.0 else if h >F 1.0 then 1.0 else h
              -- Actual height in world units
              height = maxH * hClamped + 0.005
              -- Position
              cellT = mkTransform (vec3 x (height * 0.5) z) identityQuat (vec3 1.0 1.0 1.0)
              -- Color from height
              cellColor = cmap hClamped
              cellMat = if wire
                then phong cellColor 32.0
                else phong cellColor 48.0
              -- Geometry
              cellGeom = if wire
                then sphere (stepX * 0.3)
                else roundedBox (vec3 (stepX * 0.9) height (stepZ * 0.9)) (stepX * 0.1) 4
          in mesh cellGeom cellMat [] cellT
             ∷ buildRow startX z stepX stepZ maxH wire cmap heightFn m (suc xIdx) remaining

        buildRows : Float → Float → Float → Float → Float → Bool → HeightColorMap
                  → HeightFunction M → M → ℕ → ℕ → List (SceneNode M Msg)
        buildRows _ _ _ _ _ _ _ _ _ _ zero = []
        buildRows startX startZ stepX stepZ maxH wire cmap heightFn m zIdx (suc remaining) =
          let z = startZ + natToFloat zIdx * stepZ
              rowNodes = buildRow startX z stepX stepZ maxH wire cmap heightFn m 0 resX
          in rowNodes ++L buildRows startX startZ stepX stepZ maxH wire cmap heightFn m (suc zIdx) remaining

-- Simple surface plot with default config
surfacePlot : ∀ {M Msg}
            → ControlTheme
            → HeightFunction M
            → HeightColorMap
            → Transform
            → SceneNode M Msg
surfacePlot theme = surfacePlot3D theme defaultSurfaceConfig

-- Wireframe surface
wireframeSurface : ∀ {M Msg}
                 → ControlTheme
                 → HeightFunction M
                 → GlColor
                 → Transform
                 → SceneNode M Msg
wireframeSurface theme heightFn c =
  surfacePlot3D theme wireframeSurfaceConfig heightFn (λ _ → c)

------------------------------------------------------------------------
-- Contour plot
------------------------------------------------------------------------

record ContourConfig : Set where
  constructor mkContourConfig
  field
    resolutionX   : ℕ
    resolutionZ   : ℕ
    bounds        : Vec3
    contourLevels : List Float    -- Height values for contour lines
    contourColor  : GlColor

defaultContourConfig : ContourConfig
defaultContourConfig = mkContourConfig
  30                              -- resolutionX
  30                              -- resolutionZ
  (vec3 1.0 0.3 1.0)             -- bounds
  (0.2 ∷ 0.4 ∷ 0.6 ∷ 0.8 ∷ [])  -- levels
  (rgba 0.1 0.1 0.1 1.0)         -- contourColor

-- Contour plot (shows height levels as rings)
contourPlot3D : ∀ {M Msg}
              → ControlTheme
              → ContourConfig
              → HeightFunction M
              → Transform
              → SceneNode M Msg
contourPlot3D {M} {Msg} theme config heightFn t =
  let resX = ContourConfig.resolutionX config
      resZ = ContourConfig.resolutionZ config
      bounds = ContourConfig.bounds config
      levels = ContourConfig.contourLevels config
      contourC = ContourConfig.contourColor config
  in bindChildren (buildContours resX resZ bounds levels contourC heightFn) t
  where
    buildContours : ℕ → ℕ → Vec3 → List Float → GlColor
                  → HeightFunction M → M → List (SceneNode M Msg)
    buildContours resX resZ bounds levels contourC heightFn m =
      -- Simplified: show points near contour levels
      let w = vec3X bounds
          maxH = vec3Y bounds
          d = vec3Z bounds
          stepX = w * recip (natToFloat resX)
          stepZ = d * recip (natToFloat resZ)
      in buildGrid (- (w * 0.5)) (- (d * 0.5)) stepX stepZ maxH levels contourC heightFn m 0 resZ resX
      where
        postulate recip : Float → Float
        {-# COMPILE JS recip = x => 1 / x #-}

        isNearLevel : Float → List Float → Bool
        isNearLevel _ [] = false
        isNearLevel h (lvl ∷ lvls) =
          let diff = absFloat (h - lvl)
          in if diff <F 0.05 then true else isNearLevel h lvls

        buildGridRow : Float → Float → Float → Float → Float → List Float → GlColor
                     → HeightFunction M → M → ℕ → ℕ → List (SceneNode M Msg)
        buildGridRow _ _ _ _ _ _ _ _ _ _ zero = []
        buildGridRow startX z stepX stepZ maxH levels contourC heightFn m xIdx (suc remX) =
          let x = startX + natToFloat xIdx * stepX
              h = heightFn m x z
              nodes = if isNearLevel h levels
                then (let y = maxH * h
                          dotT = mkTransform (vec3 x y z) identityQuat (vec3 1.0 1.0 1.0)
                          dotGeom = sphere (stepX * 0.25)
                          dotMat = phong contourC 32.0
                      in (mesh dotGeom dotMat [] dotT ∷ []))
                else []
          in nodes ++L buildGridRow startX z stepX stepZ maxH levels contourC heightFn m (suc xIdx) remX

        buildGrid : Float → Float → Float → Float → Float → List Float → GlColor
                  → HeightFunction M → M → ℕ → ℕ → ℕ → List (SceneNode M Msg)
        buildGrid _ _ _ _ _ _ _ _ _ _ zero _ = []
        buildGrid startX startZ stepX stepZ maxH levels contourC heightFn m zIdx (suc remZ) resX =
          let z = startZ + natToFloat zIdx * stepZ
              rowNodes = buildGridRow startX z stepX stepZ maxH levels contourC heightFn m 0 resX
          in rowNodes ++L buildGrid startX startZ stepX stepZ maxH levels contourC heightFn m (suc zIdx) remZ resX

