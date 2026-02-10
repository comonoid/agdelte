{-# OPTIONS --without-K #-}

-- SVG Pie / Donut Chart
-- Part-to-whole visualization

module Agdelte.Svg.Controls.Charts.Pie where

open import Data.String using (String; _++_)
open import Data.Float using (Float; _+_; _-_; _*_)
open import Data.Float.Base using (_÷_; _≤ᵇ_; fromℕ)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; if_then_else_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Agdelte.Reactive.Node using (Node; Attr; elem; attr; text; on)
open import Agdelte.Svg.Elements using (svg; g; path'; circle'; svgText)
open import Agdelte.Svg.Attributes
open import Agdelte.Css.Show using (showFloat)

------------------------------------------------------------------------
-- Constants
------------------------------------------------------------------------

private
  pi : Float
  pi = 3.14159265359

------------------------------------------------------------------------
-- Data types
------------------------------------------------------------------------

record PieSlice (A : Set) : Set where
  constructor mkPieSlice
  field
    sliceLabel   : String
    sliceValue   : Float
    sliceColor   : String
    sliceOnClick : Maybe A

open PieSlice public

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

private
  sumValues : ∀ {A} → List (PieSlice A) → Float
  sumValues [] = 0.0
  sumValues (s ∷ ss) = sliceValue s + sumValues ss

  -- Compute arc path for a pie slice
  -- startAngle and endAngle in radians
  arcPath : Float → Float → Float → Float → Float → String
  arcPath cx cy radius startA endA =
    let x1 = cx + radius * cos startA
        y1 = cy + radius * sin startA
        x2 = cx + radius * cos endA
        y2 = cy + radius * sin endA
        largeArc = if (endA - startA) ≤ᵇ pi then "0" else "1"
    in "M " ++ showFloat cx ++ " " ++ showFloat cy
       ++ " L " ++ showFloat x1 ++ " " ++ showFloat y1
       ++ " A " ++ showFloat radius ++ " " ++ showFloat radius
       ++ " 0 " ++ largeArc ++ " 1 "
       ++ showFloat x2 ++ " " ++ showFloat y2
       ++ " Z"
    where
      -- Simple sin/cos approximations (for demo - real impl would use primitives)
      cos sin : Float → Float
      cos x = 1.0 - (x * x ÷ 2.0) + (x * x * x * x ÷ 24.0)
      sin x = x - (x * x * x ÷ 6.0) + (x * x * x * x * x ÷ 120.0)

  -- Donut arc (two arcs connected)
  donutArcPath : Float → Float → Float → Float → Float → Float → String
  donutArcPath cx cy outer inner startA endA =
    let ox1 = cx + outer * cos startA
        oy1 = cy + outer * sin startA
        ox2 = cx + outer * cos endA
        oy2 = cy + outer * sin endA
        ix1 = cx + inner * cos endA
        iy1 = cy + inner * sin endA
        ix2 = cx + inner * cos startA
        iy2 = cy + inner * sin startA
        largeArc = if (endA - startA) ≤ᵇ pi then "0" else "1"
    in "M " ++ showFloat ox1 ++ " " ++ showFloat oy1
       ++ " A " ++ showFloat outer ++ " " ++ showFloat outer
       ++ " 0 " ++ largeArc ++ " 1 "
       ++ showFloat ox2 ++ " " ++ showFloat oy2
       ++ " L " ++ showFloat ix1 ++ " " ++ showFloat iy1
       ++ " A " ++ showFloat inner ++ " " ++ showFloat inner
       ++ " 0 " ++ largeArc ++ " 0 "
       ++ showFloat ix2 ++ " " ++ showFloat iy2
       ++ " Z"
    where
      cos sin : Float → Float
      cos x = 1.0 - (x * x ÷ 2.0) + (x * x * x * x ÷ 24.0)
      sin x = x - (x * x * x ÷ 6.0) + (x * x * x * x * x ÷ 120.0)

------------------------------------------------------------------------
-- Pie Chart
------------------------------------------------------------------------

-- | Pie chart
pieChart : ∀ {M A}
         → Float → Float           -- center x, y
         → Float                   -- radius
         → List (PieSlice A)
         → Node M A
pieChart {M} {A} cx cy radius slices =
  let total = sumValues slices
  in g ( attr "class" "svg-pie-chart" ∷ [] )
       (renderSlices cx cy radius total slices (0.0 - (pi ÷ 2.0)))
  where
    renderSlices : Float → Float → Float → Float
                 → List (PieSlice A) → Float → List (Node M A)
    renderSlices _ _ _ _ [] _ = []
    renderSlices pcx pcy r tot (s ∷ ss) startA =
      let fraction = if tot ≤ᵇ 0.0 then 0.0 else sliceValue s ÷ tot
          sweep = fraction * 2.0 * pi
          endA = startA + sweep
          pathD = arcPath pcx pcy r startA endA
      in (case sliceOnClick s of λ where
            nothing →
              path' ( d_ pathD
                    ∷ fill_ (sliceColor s)
                    ∷ attr "class" "pie-slice"
                    ∷ [] ) []
            (just msg) →
              path' ( d_ pathD
                    ∷ fill_ (sliceColor s)
                    ∷ attr "class" "pie-slice pie-slice--clickable"
                    ∷ attr "style" "cursor: pointer"
                    ∷ on "click" msg
                    ∷ [] ) [])
         ∷ renderSlices pcx pcy r tot ss endA
      where
        case_of_ : ∀ {a b} {X : Set a} {Y : Set b} → X → (X → Y) → Y
        case x of f = f x

------------------------------------------------------------------------
-- Donut Chart
------------------------------------------------------------------------

-- | Donut chart (pie with hole in center)
donutChart : ∀ {M A}
           → Float → Float         -- center
           → Float → Float         -- outer, inner radius
           → List (PieSlice A)
           → Node M A
donutChart {M} {A} cx cy outer inner slices =
  let total = sumValues slices
  in g ( attr "class" "svg-donut-chart" ∷ [] )
       (renderSlices cx cy outer inner total slices (0.0 - (pi ÷ 2.0)))
  where
    renderSlices : Float → Float → Float → Float → Float
                 → List (PieSlice A) → Float → List (Node M A)
    renderSlices _ _ _ _ _ [] _ = []
    renderSlices pcx pcy outr inr tot (s ∷ ss) startA =
      let fraction = if tot ≤ᵇ 0.0 then 0.0 else sliceValue s ÷ tot
          sweep = fraction * 2.0 * pi
          endA = startA + sweep
          pathD = donutArcPath pcx pcy outr inr startA endA
      in path' ( d_ pathD
               ∷ fill_ (sliceColor s)
               ∷ attr "class" "donut-slice"
               ∷ [] ) []
         ∷ renderSlices pcx pcy outr inr tot ss endA

------------------------------------------------------------------------
-- Donut with center content
------------------------------------------------------------------------

-- | Donut chart with content in the center
donutWithCenter : ∀ {M A}
                → Float → Float → Float → Float
                → List (PieSlice A)
                → Node M A                 -- center content
                → Node M A
donutWithCenter cx cy outer inner slices centerNode =
  g ( attr "class" "svg-donut-with-center" ∷ [] )
    ( donutChart cx cy outer inner slices
    ∷ g ( attr "transform" ("translate(" ++ showFloat cx ++ "," ++ showFloat cy ++ ")") ∷ [] )
        ( centerNode ∷ [] )
    ∷ [] )

------------------------------------------------------------------------
-- Simple constructors
------------------------------------------------------------------------

-- | Simple pie chart from label/value pairs
simplePieChart : ∀ {M A}
               → Float → Float → Float
               → List (String × Float)
               → Node M A
simplePieChart {M} {A} cx cy r pairs =
  pieChart cx cy r (toSlices pairs)
  where
    colors : List String
    colors = "#3b82f6" ∷ "#22c55e" ∷ "#f59e0b" ∷ "#ef4444" ∷ "#8b5cf6"
           ∷ "#ec4899" ∷ "#14b8a6" ∷ "#f97316" ∷ []

    getColor : ℕ → String
    getColor n = go colors n
      where
        go : List String → ℕ → String
        go [] _ = "#3b82f6"
        go (c ∷ _) zero = c
        go (_ ∷ cs) (suc m) = go cs m

    toSlices : List (String × Float) → List (PieSlice A)
    toSlices xs = go xs 0
      where
        go : List (String × Float) → ℕ → List (PieSlice A)
        go [] _ = []
        go ((lbl , val) ∷ rest) idx =
          mkPieSlice lbl val (getColor idx) nothing
          ∷ go rest (suc idx)
