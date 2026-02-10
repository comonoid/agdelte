{-# OPTIONS --without-K #-}

-- SVG Scatter Plot
-- Correlation and distribution visualization

module Agdelte.Svg.Controls.Charts.Scatter where

open import Data.String using (String; _++_)
open import Data.Float using (Float; _+_; _-_; _*_)
open import Data.Float.Base using (_÷_; _≤ᵇ_; _<ᵇ_; fromℕ)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; if_then_else_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Agdelte.Reactive.Node using (Node; Attr; elem; attr; text; on)
open import Agdelte.Svg.Elements using (svg; g; circle'; svgText)
open import Agdelte.Svg.Attributes
open import Agdelte.Css.Show using (showFloat)

------------------------------------------------------------------------
-- Data types
------------------------------------------------------------------------

record ScatterPoint (A : Set) : Set where
  constructor mkScatterPoint
  field
    spX       : Float
    spY       : Float
    spSize    : Float           -- radius
    spColor   : String
    spLabel   : Maybe String
    spOnClick : Maybe A

open ScatterPoint public

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

private
  findMinMax : List Float → Float → Float → Float × Float
  findMinMax [] minA maxA = (minA , maxA)
  findMinMax (v ∷ vs) minA maxA =
    findMinMax vs
      (if v <ᵇ minA then v else minA)
      (if maxA <ᵇ v then v else maxA)
    where
      open import Data.Product using (_×_; _,_)

  extractXs extractYs : ∀ {A} → List (ScatterPoint A) → List Float
  extractXs [] = []
  extractXs (p ∷ ps) = spX p ∷ extractXs ps
  extractYs [] = []
  extractYs (p ∷ ps) = spY p ∷ extractYs ps

  scaleVal : Float → Float → Float → Float → Float → Float
  scaleVal minV maxV size offset v =
    let range = if (maxV - minV) ≤ᵇ 0.0 then 1.0 else maxV - minV
    in offset + ((v - minV) ÷ range) * size

------------------------------------------------------------------------
-- Scatter Plot
------------------------------------------------------------------------

-- | Scatter plot
scatterPlot : ∀ {M A}
            → Float → Float → Float → Float  -- x, y, width, height
            → List (ScatterPoint A)
            → Node M A
scatterPlot {M} {A} px py w h points =
  let xs = extractXs points
      ys = extractYs points
      (minX , maxX) = findMinMax xs 1.0e10 (0.0 - 1.0e10)
      (minY , maxY) = findMinMax ys 1.0e10 (0.0 - 1.0e10)
  in g ( attr "class" "svg-scatter-plot" ∷ [] )
       (renderPoints px py w h minX maxX minY maxY points)
  where
    open import Data.Product using (_×_; _,_)

    renderPoints : Float → Float → Float → Float
                 → Float → Float → Float → Float
                 → List (ScatterPoint A) → List (Node M A)
    renderPoints _ _ _ _ _ _ _ _ [] = []
    renderPoints px' py' w' h' minX maxX minY maxY (p ∷ ps) =
      let sx = scaleVal minX maxX w' px' (spX p)
          sy = py' + h' - scaleVal minY maxY h' 0.0 (spY p)
      in (case spOnClick p of λ where
            nothing →
              circle' ( cxF sx ∷ cyF sy
                      ∷ rF (spSize p)
                      ∷ fill_ (spColor p)
                      ∷ attr "class" "scatter-point"
                      ∷ [] ) []
            (just msg) →
              circle' ( cxF sx ∷ cyF sy
                      ∷ rF (spSize p)
                      ∷ fill_ (spColor p)
                      ∷ attr "class" "scatter-point scatter-point--clickable"
                      ∷ attr "style" "cursor: pointer"
                      ∷ on "click" msg
                      ∷ [] ) [])
         ∷ renderPoints px' py' w' h' minX maxX minY maxY ps
      where
        case_of_ : ∀ {a b} {X : Set a} {Y : Set b} → X → (X → Y) → Y
        case x of f = f x

------------------------------------------------------------------------
-- Simple scatter plot
------------------------------------------------------------------------

-- | Simple scatter plot from (x, y) pairs
simpleScatterPlot : ∀ {M A}
                  → Float → Float → Float → Float
                  → Float                      -- point radius
                  → String                     -- color
                  → List (Float × Float)
                  → Node M A
simpleScatterPlot {M} {A} px py w h radius color pairs =
  scatterPlot px py w h (toPoints pairs)
  where
    toPoints : List (Float × Float) → List (ScatterPoint A)
    toPoints [] = []
    toPoints ((vx , vy) ∷ rest) =
      mkScatterPoint vx vy radius color nothing nothing
      ∷ toPoints rest

------------------------------------------------------------------------
-- Bubble chart
------------------------------------------------------------------------

-- | Bubble chart (scatter with size dimension)
bubbleChart : ∀ {M A}
            → Float → Float → Float → Float
            → Float                            -- max bubble radius
            → List (ScatterPoint A)
            → Node M A
bubbleChart {M} {A} px py w h maxR points =
  let maxSize = findMaxSize points 0.0
  in g ( attr "class" "svg-bubble-chart" ∷ [] )
       (renderBubbles px py w h maxR maxSize points)
  where
    findMaxSize : List (ScatterPoint A) → Float → Float
    findMaxSize [] acc = acc
    findMaxSize (p ∷ ps) acc =
      findMaxSize ps (if acc <ᵇ spSize p then spSize p else acc)

    open import Data.Product using (_×_; _,_)

    xs = extractXs points
    ys = extractYs points
    bounds = (findMinMax xs 1.0e10 (0.0 - 1.0e10) ,
              findMinMax ys 1.0e10 (0.0 - 1.0e10))

    renderBubbles : Float → Float → Float → Float → Float → Float
                  → List (ScatterPoint A) → List (Node M A)
    renderBubbles _ _ _ _ _ _ [] = []
    renderBubbles px' py' w' h' maxR' maxS (p ∷ ps) =
      let (minX , maxX) , (minY , maxY) = bounds
          sx = scaleVal minX maxX w' px' (spX p)
          sy = py' + h' - scaleVal minY maxY h' 0.0 (spY p)
          r = if maxS ≤ᵇ 0.0 then 0.0 else (spSize p ÷ maxS) * maxR'
      in circle' ( cxF sx ∷ cyF sy
                 ∷ rF r
                 ∷ fill_ (spColor p)
                 ∷ attr "opacity" "0.6"
                 ∷ attr "class" "bubble"
                 ∷ [] ) []
         ∷ renderBubbles px' py' w' h' maxR' maxS ps
