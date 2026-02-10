{-# OPTIONS --without-K #-}

-- SVG Area Chart
-- Filled area visualization for time series and comparisons

module Agdelte.Svg.Controls.Charts.Area where

open import Data.String using (String; _++_)
open import Data.Float using (Float; _+_; _-_; _*_)
open import Data.Float.Base using (_÷_; _≤ᵇ_; _<ᵇ_; fromℕ)
open import Data.List using (List; []; _∷_; map; zip; foldr) renaming (_++_ to _++ᴸ_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Agdelte.Reactive.Node using (Node; Attr; elem; attr; text)
open import Agdelte.Svg.Elements using (svg; g; path'; circle'; svgText; line')
open import Agdelte.Svg.Attributes
open import Agdelte.Css.Show using (showFloat)

------------------------------------------------------------------------
-- Data types
------------------------------------------------------------------------

record DataPoint : Set where
  constructor mkDataPoint
  field
    dpX : Float
    dpY : Float

open DataPoint public

record AreaSeries : Set where
  constructor mkAreaSeries
  field
    areaName  : String
    areaColor : String
    areaData  : List DataPoint

open AreaSeries public

record AreaChartConfig : Set where
  constructor mkAreaConfig
  field
    cfgWidth     : Float
    cfgHeight    : Float
    cfgShowGrid  : Bool
    cfgShowDots  : Bool
    cfgShowLine  : Bool
    cfgOpacity   : Float           -- area fill opacity (0.0 to 1.0)
    cfgAnimated  : Bool

open AreaChartConfig public

defaultAreaConfig : Float → Float → AreaChartConfig
defaultAreaConfig w h = mkAreaConfig w h true false true 0.4 false

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

private
  findMin : List Float → Float → Float
  findMin [] acc = acc
  findMin (v ∷ vs) acc = findMin vs (if v <ᵇ acc then v else acc)

  findMax : List Float → Float → Float
  findMax [] acc = acc
  findMax (v ∷ vs) acc = findMax vs (if acc <ᵇ v then v else acc)

  extractX extractY : List DataPoint → List Float
  extractX [] = []
  extractX (p ∷ ps) = dpX p ∷ extractX ps
  extractY [] = []
  extractY (p ∷ ps) = dpY p ∷ extractY ps

  scaleX : Float → Float → Float → Float → Float → Float
  scaleX minX maxX w px vx =
    let range = if (maxX - minX) ≤ᵇ 0.0 then 1.0 else maxX - minX
    in px + ((vx - minX) ÷ range) * w

  scaleY : Float → Float → Float → Float → Float → Float
  scaleY minY maxY h py vy =
    let range = if (maxY - minY) ≤ᵇ 0.0 then 1.0 else maxY - minY
    in py + h - ((vy - minY) ÷ range) * h

  -- Collect all X/Y from all series
  allXs : List AreaSeries → List Float
  allXs [] = []
  allXs (s ∷ ss) = extractX (areaData s) ++ᴸ allXs ss

  allYs : List AreaSeries → List Float
  allYs [] = []
  allYs (s ∷ ss) = extractY (areaData s) ++ᴸ allYs ss

------------------------------------------------------------------------
-- Grid rendering
------------------------------------------------------------------------

private
  renderGrid : ∀ {M A} → Float → Float → Float → Float → ℕ → ℕ → Node M A
  renderGrid px py w h xTicks yTicks =
    g ( attr "class" "area-chart-grid" ∷ [] )
      ( renderHLines px py w h yTicks 0
      ++ᴸ renderVLines px py w h xTicks 0 )
    where

      renderHLines : ∀ {M A} → Float → Float → Float → Float → ℕ → ℕ → List (Node M A)
      renderHLines _ _ _ _ zero _ = []
      renderHLines px' py' w' h' (suc n) idx =
        let yPos = py' + (fromℕ idx ÷ fromℕ (suc n)) * h'
        in line' ( x1F px' ∷ y1F yPos
                 ∷ x2F (px' + w') ∷ y2F yPos
                 ∷ stroke_ "#e5e7eb"
                 ∷ strokeWidthF 1.0
                 ∷ [] ) []
           ∷ renderHLines px' py' w' h' n (suc idx)

      renderVLines : ∀ {M A} → Float → Float → Float → Float → ℕ → ℕ → List (Node M A)
      renderVLines _ _ _ _ zero _ = []
      renderVLines px' py' w' h' (suc n) idx =
        let xPos = px' + (fromℕ idx ÷ fromℕ (suc n)) * w'
        in line' ( x1F xPos ∷ y1F py'
                 ∷ x2F xPos ∷ y2F (py' + h')
                 ∷ stroke_ "#e5e7eb"
                 ∷ strokeWidthF 1.0
                 ∷ [] ) []
           ∷ renderVLines px' py' w' h' n (suc idx)

------------------------------------------------------------------------
-- Path building for area
------------------------------------------------------------------------

private
  buildAreaPath : Float → Float → Float → Float
                → Float → Float → Float → Float
                → List DataPoint → String
  buildAreaPath px py w h minX maxX minY maxY pts =
    let line = buildLine pts 0
        (firstX , lastX) = getFirstLastX pts
        baseY = py + h
    in line ++ " L " ++ showFloat lastX ++ " " ++ showFloat baseY
       ++ " L " ++ showFloat firstX ++ " " ++ showFloat baseY ++ " Z"
    where
      buildLine : List DataPoint → ℕ → String
      buildLine [] _ = ""
      buildLine (p ∷ ps) idx =
        let sx = scaleX minX maxX w px (dpX p)
            sy = scaleY minY maxY h py (dpY p)
            pre = if idx ≡ᵇ 0 then "M " else " L "
        in pre ++ showFloat sx ++ " " ++ showFloat sy ++ buildLine ps (suc idx)
        where
          open import Data.Nat using (_≡ᵇ_)

      getFirstLastX : List DataPoint → Float × Float
      getFirstLastX [] = (px , px)
      getFirstLastX (p ∷ []) = let sx = scaleX minX maxX w px (dpX p) in (sx , sx)
      getFirstLastX (p ∷ ps) = (scaleX minX maxX w px (dpX p) , getLast ps)
        where
          getLast : List DataPoint → Float
          getLast [] = px
          getLast (q ∷ []) = scaleX minX maxX w px (dpX q)
          getLast (_ ∷ qs) = getLast qs

  buildLinePath : Float → Float → Float → Float
                → Float → Float → Float → Float
                → List DataPoint → String
  buildLinePath px py w h minX maxX minY maxY pts = go pts 0
    where
      go : List DataPoint → ℕ → String
      go [] _ = ""
      go (p ∷ ps) idx =
        let sx = scaleX minX maxX w px (dpX p)
            sy = scaleY minY maxY h py (dpY p)
            pre = if idx ≡ᵇ 0 then "M " else " L "
        in pre ++ showFloat sx ++ " " ++ showFloat sy ++ go ps (suc idx)
        where
          open import Data.Nat using (_≡ᵇ_)

------------------------------------------------------------------------
-- Simple Area Chart
------------------------------------------------------------------------

-- | Simple single-series area chart
simpleAreaChart : ∀ {M A}
                → Float → Float → Float → Float  -- x, y, width, height
                → String                          -- color
                → Float                           -- opacity
                → List DataPoint
                → Node M A
simpleAreaChart {M} {A} px py w h color opacity pts =
  let xs = extractX pts
      ys = extractY pts
      minX = findMin xs 1.0e10
      maxX = findMax xs (0.0 - 1.0e10)
      minY = findMin ys 1.0e10
      maxY = findMax ys (0.0 - 1.0e10)
      areaPath = buildAreaPath px py w h minX maxX minY maxY pts
      linePath = buildLinePath px py w h minX maxX minY maxY pts
  in g ( attr "class" "svg-area-chart" ∷ [] )
       ( -- Filled area
         path' ( d_ areaPath
               ∷ fill_ color
               ∷ attr "opacity" (showFloat opacity)
               ∷ [] ) []
       -- Top line
       ∷ path' ( d_ linePath
               ∷ fill_ "none"
               ∷ stroke_ color
               ∷ strokeWidthF 2.0
               ∷ attr "stroke-linecap" "round"
               ∷ attr "stroke-linejoin" "round"
               ∷ [] ) []
       ∷ [] )

------------------------------------------------------------------------
-- Multi-series Area Chart
------------------------------------------------------------------------

-- | Area chart with multiple overlapping series
multiAreaChart : ∀ {M A}
               → Float → Float → Float → Float
               → Float                            -- opacity
               → List AreaSeries
               → Node M A
multiAreaChart {M} {A} px py w h opacity series =
  let allX = allXs series
      allY = allYs series
      minX = findMin allX 1.0e10
      maxX = findMax allX (0.0 - 1.0e10)
      minY = findMin allY 1.0e10
      maxY = findMax allY (0.0 - 1.0e10)
  in g ( attr "class" "svg-multi-area-chart" ∷ [] )
       (renderAllSeries px py w h minX maxX minY maxY opacity series)
  where
    renderAllSeries : Float → Float → Float → Float
                    → Float → Float → Float → Float → Float
                    → List AreaSeries → List (Node M A)
    renderAllSeries _ _ _ _ _ _ _ _ _ [] = []
    renderAllSeries px' py' w' h' minX' maxX' minY' maxY' op (s ∷ ss) =
      let areaPath = buildAreaPath px' py' w' h' minX' maxX' minY' maxY' (areaData s)
          linePath = buildLinePath px' py' w' h' minX' maxX' minY' maxY' (areaData s)
      in g ( attr "class" ("series-" ++ areaName s) ∷ [] )
           ( path' ( d_ areaPath
                   ∷ fill_ (areaColor s)
                   ∷ attr "opacity" (showFloat op)
                   ∷ [] ) []
           ∷ path' ( d_ linePath
                   ∷ fill_ "none"
                   ∷ stroke_ (areaColor s)
                   ∷ strokeWidthF 2.0
                   ∷ [] ) []
           ∷ [] )
         ∷ renderAllSeries px' py' w' h' minX' maxX' minY' maxY' op ss

------------------------------------------------------------------------
-- Stacked Area Chart
------------------------------------------------------------------------

-- | Stacked area chart (series stacked on top of each other)
stackedAreaChart : ∀ {M A}
                 → Float → Float → Float → Float
                 → List String                    -- colors
                 → List (List DataPoint)          -- series data
                 → Node M A
stackedAreaChart {M} {A} px py w h colors allData =
  let xs = getXsFromFirst allData
      minX = findMin xs 1.0e10
      maxX = findMax xs (0.0 - 1.0e10)
      stackedData = computeStacks allData
      maxY = findMaxStacked stackedData
  in g ( attr "class" "svg-stacked-area-chart" ∷ [] )
       (renderStacked px py w h minX maxX 0.0 maxY colors stackedData [])
  where
    getXsFromFirst : List (List DataPoint) → List Float
    getXsFromFirst [] = []
    getXsFromFirst (pts ∷ _) = extractX pts

    -- Add up Y values at each X position
    addPoints : List DataPoint → List DataPoint → List DataPoint
    addPoints [] _ = []
    addPoints _ [] = []
    addPoints (p ∷ ps) (q ∷ qs) =
      mkDataPoint (dpX p) (dpY p + dpY q) ∷ addPoints ps qs

    computeStacks : List (List DataPoint) → List (List DataPoint)
    computeStacks [] = []
    computeStacks (first ∷ rest) = go first rest
      where
        go : List DataPoint → List (List DataPoint) → List (List DataPoint)
        go acc [] = acc ∷ []
        go acc (pts ∷ more) =
          let newAcc = addPoints acc pts
          in acc ∷ go newAcc more

    findMaxStacked : List (List DataPoint) → Float
    findMaxStacked [] = 0.0
    findMaxStacked (pts ∷ rest) =
      let m = findMax (extractY pts) 0.0
          r = findMaxStacked rest
      in if r <ᵇ m then m else r

    reverse' : List DataPoint → List DataPoint
    reverse' = go []
      where
        go : List DataPoint → List DataPoint → List DataPoint
        go acc [] = acc
        go acc (x ∷ xs) = go (x ∷ acc) xs

    buildStackPath : Float → Float → Float → Float
                   → Float → Float → Float → Float
                   → List DataPoint → List DataPoint → String
    buildStackPath px' py' w' h' minX' maxX' minY' maxY' top bottom =
      let topLine = goForward top 0
          bottomLine = goBackward (reverse' bottom)
      in topLine ++ bottomLine ++ " Z"
      where
        open import Data.Nat using (_≡ᵇ_)

        goForward : List DataPoint → ℕ → String
        goForward [] _ = ""
        goForward (p ∷ ps) idx =
          let sx = scaleX minX' maxX' w' px' (dpX p)
              sy = scaleY minY' maxY' h' py' (dpY p)
              pre = if idx ≡ᵇ 0 then "M " else " L "
          in pre ++ showFloat sx ++ " " ++ showFloat sy ++ goForward ps (suc idx)

        goBackward : List DataPoint → String
        goBackward [] = ""
        goBackward (p ∷ ps) =
          let sx = scaleX minX' maxX' w' px' (dpX p)
              sy = scaleY minY' maxY' h' py' (dpY p)
          in " L " ++ showFloat sx ++ " " ++ showFloat sy ++ goBackward ps

    -- Render from top to bottom (last series first for correct stacking)
    renderStacked : Float → Float → Float → Float
                  → Float → Float → Float → Float
                  → List String → List (List DataPoint) → List (List DataPoint)
                  → List (Node M A)
    renderStacked _ _ _ _ _ _ _ _ _ [] _ = []
    renderStacked px' py' w' h' minX' maxX' minY' maxY' (c ∷ cs) (top ∷ rest) prev =
      let bottom = case prev of λ where
            [] → map (λ p → mkDataPoint (dpX p) 0.0) top
            (b ∷ _) → b
          stackPath = buildStackPath px' py' w' h' minX' maxX' minY' maxY' top bottom
      in path' ( d_ stackPath
               ∷ fill_ c
               ∷ attr "opacity" "0.8"
               ∷ [] ) []
         ∷ renderStacked px' py' w' h' minX' maxX' minY' maxY' cs rest (top ∷ prev)
      where
        case_of_ : ∀ {a b} {X : Set a} {Y : Set b} → X → (X → Y) → Y
        case x of f = f x
    renderStacked _ _ _ _ _ _ _ _ [] _ _ = []

------------------------------------------------------------------------
-- Area Chart with Grid
------------------------------------------------------------------------

-- | Area chart with background grid
areaChartWithGrid : ∀ {M A}
                  → Float → Float → Float → Float
                  → String → Float
                  → ℕ → ℕ                         -- x and y tick count
                  → List DataPoint
                  → Node M A
areaChartWithGrid {M} {A} px py w h color opacity xTicks yTicks pts =
  g ( attr "class" "svg-area-chart-grid" ∷ [] )
    ( renderGrid px py w h xTicks yTicks
    ∷ simpleAreaChart px py w h color opacity pts
    ∷ [] )

------------------------------------------------------------------------
-- Quick constructors
------------------------------------------------------------------------

-- | Blue area chart with default opacity
blueAreaChart : ∀ {M A}
              → Float → Float → Float → Float
              → List DataPoint
              → Node M A
blueAreaChart px py w h pts =
  simpleAreaChart px py w h "#3b82f6" 0.4 pts

-- | Green area chart
greenAreaChart : ∀ {M A}
               → Float → Float → Float → Float
               → List DataPoint
               → Node M A
greenAreaChart px py w h pts =
  simpleAreaChart px py w h "#22c55e" 0.4 pts

-- | Gradient-style area (darker at bottom)
gradientAreaChart : ∀ {M A}
                  → Float → Float → Float → Float
                  → String                        -- color
                  → List DataPoint
                  → Node M A
gradientAreaChart px py w h color pts =
  simpleAreaChart px py w h color 0.6 pts
