{-# OPTIONS --without-K #-}

-- SVG Gradient Helpers
-- Typed gradient definitions

module Agdelte.Svg.Gradient where

open import Data.Float using (Float; _*_)
open import Data.List using (List; []; _∷_; map)
open import Data.String using (String; _++_)
open import Agdelte.Css.Show using (showFloat)
open import Agdelte.Css.Color using (Color; showColor)
open import Agdelte.Reactive.Node using (Node; Attr; attr; elem)

------------------------------------------------------------------------
-- Gradient Stop
------------------------------------------------------------------------

record GradientStop : Set where
  constructor mkStop
  field
    offset'  : Float        -- 0.0 to 1.0
    color   : Color
    opacity : Float         -- 0.0 to 1.0 (1.0 = fully opaque)

open GradientStop public

-- Simple stop (fully opaque)
stop : Float → Color → GradientStop
stop o c = mkStop o c 1.0

-- Render stop element
renderStop : ∀ {M Msg} → GradientStop → Node M Msg
renderStop s = elem "stop"
  ( attr "offset" (showFloat (offset' s * 100.0) ++ "%")
  ∷ attr "stop-color" (showColor (color s))
  ∷ attr "stop-opacity" (showFloat (opacity s))
  ∷ []) []

------------------------------------------------------------------------
-- Linear Gradient
------------------------------------------------------------------------

record LinearGradient : Set where
  constructor mkLinearGradient
  field
    gradId : String
    x1' y1' x2' y2' : Float    -- direction (0-1 coordinates)
    stops  : List GradientStop

open LinearGradient public

-- Common gradients
horizontalGradient : String → List GradientStop → LinearGradient
horizontalGradient gid ss = mkLinearGradient gid 0.0 0.0 1.0 0.0 ss

verticalGradient : String → List GradientStop → LinearGradient
verticalGradient gid ss = mkLinearGradient gid 0.0 0.0 0.0 1.0 ss

diagonalGradient : String → List GradientStop → LinearGradient
diagonalGradient gid ss = mkLinearGradient gid 0.0 0.0 1.0 1.0 ss

-- Render linear gradient element (goes in defs)
renderLinearGradient : ∀ {M Msg} → LinearGradient → Node M Msg
renderLinearGradient g = elem "linearGradient"
  ( attr "id" (gradId g)
  ∷ attr "x1" (showFloat (x1' g * 100.0) ++ "%")
  ∷ attr "y1" (showFloat (y1' g * 100.0) ++ "%")
  ∷ attr "x2" (showFloat (x2' g * 100.0) ++ "%")
  ∷ attr "y2" (showFloat (y2' g * 100.0) ++ "%")
  ∷ [])
  (map renderStop (stops g))

------------------------------------------------------------------------
-- Radial Gradient
------------------------------------------------------------------------

record RadialGradient : Set where
  constructor mkRadialGradient
  field
    gradId : String
    cx' cy' : Float      -- center (0-1)
    r'     : Float       -- radius (0-1)
    fx' fy' : Float      -- focal point (0-1)
    stops  : List GradientStop

-- Simple radial gradient (center = focal point)
simpleRadialGradient : String → List GradientStop → RadialGradient
simpleRadialGradient gid ss = mkRadialGradient gid 0.5 0.5 0.5 0.5 0.5 ss

-- Render radial gradient element
renderRadialGradient : ∀ {M Msg} → RadialGradient → Node M Msg
renderRadialGradient g = elem "radialGradient"
  ( attr "id" (RadialGradient.gradId g)
  ∷ attr "cx" (showFloat (RadialGradient.cx' g * 100.0) ++ "%")
  ∷ attr "cy" (showFloat (RadialGradient.cy' g * 100.0) ++ "%")
  ∷ attr "r" (showFloat (RadialGradient.r' g * 100.0) ++ "%")
  ∷ attr "fx" (showFloat (RadialGradient.fx' g * 100.0) ++ "%")
  ∷ attr "fy" (showFloat (RadialGradient.fy' g * 100.0) ++ "%")
  ∷ [])
  (map renderStop (RadialGradient.stops g))

------------------------------------------------------------------------
-- URL reference helper
------------------------------------------------------------------------

-- Use gradient: fill="url(#gradientId)"
url : String → String
url gid = "url(#" ++ gid ++ ")"
