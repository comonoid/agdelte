{-# OPTIONS --without-K #-}

-- SVG Progress Ring
-- Circular progress indicator

module Agdelte.Svg.Controls.Gauges.ProgressRing where

open import Data.String using (String; _++_)
open import Data.Float using (Float; _+_; _-_; _*_)
open import Data.Float.Base using (_÷_; _≤ᵇ_; _<ᵇ_; fromℕ)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Agdelte.Reactive.Node using (Node; Attr; elem; attr; text)
open import Agdelte.Svg.Elements using (svg; g; path'; circle'; svgText)
open import Agdelte.Svg.Attributes
open import Agdelte.Css.Show using (showFloat)

------------------------------------------------------------------------
-- Constants
------------------------------------------------------------------------

private
  pi : Float
  pi = 3.14159265359

  sin : Float → Float
  sin x = x - (x * x * x ÷ 6.0)
        + (x * x * x * x * x ÷ 120.0)
        - (x * x * x * x * x * x * x ÷ 5040.0)

  cos : Float → Float
  cos x = 1.0 - (x * x ÷ 2.0)
        + (x * x * x * x ÷ 24.0)
        - (x * x * x * x * x * x ÷ 720.0)

------------------------------------------------------------------------
-- Simple Progress Ring
------------------------------------------------------------------------

-- | Basic progress ring (0.0 to 1.0)
progressRing : ∀ {M A}
             → Float → Float          -- center x, y
             → Float                   -- radius
             → Float                   -- stroke width
             → String                  -- color
             → Float                   -- progress (0.0 to 1.0)
             → Node M A
progressRing cx cy radius strokeW color progress =
  let clampedP = if progress <ᵇ 0.0 then 0.0
                 else if 1.0 <ᵇ progress then 1.0 else progress
      circumference = 2.0 * pi * radius
      offset = circumference * (1.0 - clampedP)
  in g ( attr "class" "svg-progress-ring" ∷ [] )
       ( -- Background circle
         circle' ( cxF cx ∷ cyF cy
                 ∷ rF radius
                 ∷ fill_ "none"
                 ∷ stroke_ "#e5e7eb"
                 ∷ strokeWidthF strokeW
                 ∷ [] ) []
       -- Progress arc (using stroke-dasharray trick)
       ∷ circle' ( cxF cx ∷ cyF cy
                 ∷ rF radius
                 ∷ fill_ "none"
                 ∷ stroke_ color
                 ∷ strokeWidthF strokeW
                 ∷ attr "stroke-linecap" "round"
                 ∷ attr "stroke-dasharray" (showFloat circumference)
                 ∷ attr "stroke-dashoffset" (showFloat offset)
                 ∷ attr "transform" ("rotate(-90 " ++ showFloat cx ++ " " ++ showFloat cy ++ ")")
                 ∷ [] ) []
       ∷ [] )

------------------------------------------------------------------------
-- Progress Ring with Label
------------------------------------------------------------------------

-- | Progress ring with centered percentage label
progressRingLabeled : ∀ {M A}
                    → Float → Float → Float → Float
                    → String
                    → Float                    -- progress
                    → String                   -- label format (use "{}" for value)
                    → Node M A
progressRingLabeled cx cy radius strokeW color progress label =
  let pct = progress * 100.0
      labelText = formatLabel label pct
  in g ( attr "class" "svg-progress-ring-labeled" ∷ [] )
       ( progressRing cx cy radius strokeW color progress
       ∷ svgText ( xF cx ∷ yF cy
                 ∷ attr "text-anchor" "middle"
                 ∷ attr "dominant-baseline" "middle"
                 ∷ attr "font-size" (showFloat (radius * 0.5))
                 ∷ attr "font-weight" "bold"
                 ∷ fill_ "#1e293b"
                 ∷ [] )
           ( text labelText ∷ [] )
       ∷ [] )
  where
    formatLabel : String → Float → String
    formatLabel lbl val = showFloat val ++ "%"  -- simplified

------------------------------------------------------------------------
-- Progress Ring with Icon
------------------------------------------------------------------------

-- | Progress ring with icon or content in center
progressRingWithContent : ∀ {M A}
                        → Float → Float → Float → Float
                        → String
                        → Float
                        → Node M A              -- center content
                        → Node M A
progressRingWithContent cx cy radius strokeW color progress content =
  g ( attr "class" "svg-progress-ring-content" ∷ [] )
    ( progressRing cx cy radius strokeW color progress
    ∷ g ( attr "transform" ("translate(" ++ showFloat cx ++ "," ++ showFloat cy ++ ")") ∷ [] )
        ( content ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- Multi-segment Progress Ring
------------------------------------------------------------------------

-- | Progress ring with multiple colored segments
multiProgressRing : ∀ {M A}
                  → Float → Float → Float → Float
                  → List (Float × String)     -- (value, color) pairs
                  → Node M A
multiProgressRing {M} {A} cx cy radius strokeW segments =
  let total = sumValues segments
      circumference = 2.0 * pi * radius
  in g ( attr "class" "svg-multi-progress-ring" ∷ [] )
       ( -- Background
         circle' ( cxF cx ∷ cyF cy
                 ∷ rF radius
                 ∷ fill_ "none"
                 ∷ stroke_ "#e5e7eb"
                 ∷ strokeWidthF strokeW
                 ∷ [] ) []
       ∷ g [] (renderSegments cx cy radius strokeW circumference total segments 0.0)
       ∷ [] )
  where
    sumValues : List (Float × String) → Float
    sumValues [] = 0.0
    sumValues ((v , _) ∷ rest) = v + sumValues rest

    renderSegments : Float → Float → Float → Float → Float → Float
                   → List (Float × String) → Float → List (Node M A)
    renderSegments _ _ _ _ _ _ [] _ = []
    renderSegments scx scy sr sw circ tot ((v , c) ∷ rest) offset =
      let segLen = if tot ≤ᵇ 0.0 then 0.0 else (v ÷ tot) * circ
          rotAngle = (offset ÷ tot) * 360.0 - 90.0
      in circle' ( cxF scx ∷ cyF scy
                 ∷ rF sr
                 ∷ fill_ "none"
                 ∷ stroke_ c
                 ∷ strokeWidthF sw
                 ∷ attr "stroke-dasharray" (showFloat segLen ++ " " ++ showFloat circ)
                 ∷ attr "transform" ("rotate(" ++ showFloat rotAngle ++ " " ++ showFloat scx ++ " " ++ showFloat scy ++ ")")
                 ∷ [] ) []
         ∷ renderSegments scx scy sr sw circ tot rest (offset + v)

------------------------------------------------------------------------
-- Gradient Progress Ring
------------------------------------------------------------------------

-- | Progress ring with gradient effect (using multiple circles)
gradientProgressRing : ∀ {M A}
                     → Float → Float → Float → Float
                     → String                  -- start color
                     → String                  -- end color
                     → Float                   -- progress
                     → Node M A
gradientProgressRing cx cy radius strokeW startColor endColor progress =
  -- Simplified: just use end color with opacity variation
  -- Real gradient would need defs/linearGradient
  g ( attr "class" "svg-gradient-progress-ring" ∷ [] )
    ( progressRing cx cy radius strokeW endColor progress
    ∷ [] )

------------------------------------------------------------------------
-- Animated Progress Ring (using CSS animation)
------------------------------------------------------------------------

-- | Indeterminate progress ring (spinning)
indeterminateRing : ∀ {M A}
                  → Float → Float → Float → Float
                  → String
                  → Node M A
indeterminateRing cx cy radius strokeW color =
  let circumference = 2.0 * pi * radius
  in g ( attr "class" "svg-indeterminate-ring" ∷ [] )
       ( -- Background
         circle' ( cxF cx ∷ cyF cy
                 ∷ rF radius
                 ∷ fill_ "none"
                 ∷ stroke_ "#e5e7eb"
                 ∷ strokeWidthF strokeW
                 ∷ [] ) []
       -- Spinning segment
       ∷ circle' ( cxF cx ∷ cyF cy
                 ∷ rF radius
                 ∷ fill_ "none"
                 ∷ stroke_ color
                 ∷ strokeWidthF strokeW
                 ∷ attr "stroke-linecap" "round"
                 ∷ attr "stroke-dasharray" (showFloat (circumference * 0.25) ++ " " ++ showFloat (circumference * 0.75))
                 ∷ attr "class" "animate-spin"
                 ∷ [] ) []
       ∷ [] )

------------------------------------------------------------------------
-- Progress Ring Group (multiple rings)
------------------------------------------------------------------------

-- | Concentric progress rings
concentricRings : ∀ {M A}
                → Float → Float              -- center
                → Float                       -- largest radius
                → Float                       -- stroke width
                → Float                       -- gap between rings
                → List (Float × String)       -- (progress, color) per ring
                → Node M A
concentricRings {M} {A} cx cy baseRadius strokeW gap rings =
  g ( attr "class" "svg-concentric-rings" ∷ [] )
    (renderRings cx cy baseRadius strokeW gap rings 0)
  where
    renderRings : Float → Float → Float → Float → Float
                → List (Float × String) → ℕ → List (Node M A)
    renderRings _ _ _ _ _ [] _ = []
    renderRings rcx rcy r sw gp ((p , c) ∷ rest) idx =
      let ringR = r - fromℕ idx * (sw + gp)
      in progressRing rcx rcy ringR sw c p
         ∷ renderRings rcx rcy r sw gp rest (suc idx)

------------------------------------------------------------------------
-- Quick constructors
------------------------------------------------------------------------

-- | Simple percentage ring
percentRing : ∀ {M A}
            → Float → Float → Float
            → Float                    -- percentage 0-100
            → Node M A
percentRing cx cy radius pct =
  progressRingLabeled cx cy radius 8.0 "#3b82f6" (pct ÷ 100.0) "{}"

-- | Green success ring
successRing : ∀ {M A}
            → Float → Float → Float
            → Float
            → Node M A
successRing cx cy radius progress =
  progressRing cx cy radius 8.0 "#22c55e" progress

-- | Red warning ring
warningRing : ∀ {M A}
            → Float → Float → Float
            → Float
            → Node M A
warningRing cx cy radius progress =
  progressRing cx cy radius 8.0 "#ef4444" progress

-- | Thin progress ring
thinRing : ∀ {M A}
         → Float → Float → Float
         → String → Float
         → Node M A
thinRing cx cy radius color progress =
  progressRing cx cy radius 3.0 color progress

-- | Thick progress ring
thickRing : ∀ {M A}
          → Float → Float → Float
          → String → Float
          → Node M A
thickRing cx cy radius color progress =
  progressRing cx cy radius 12.0 color progress
