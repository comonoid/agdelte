{-# OPTIONS --without-K #-}

-- SVG Line Chart
-- Time series and trend visualization

module Agdelte.Svg.Controls.Charts.Line where

open import Data.String using (String; _++_)
open import Data.Float using (Float; _+_; _-_; _*_)
open import Data.Float.Base using (_÷_; _≤ᵇ_; _<ᵇ_; fromℕ)
open import Data.List using (List; []; _∷_; length)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)

open import Agdelte.Reactive.Node using (Node; Attr; elem; attr; text;
  attrBind; stringBinding; Binding)
open import Agdelte.Svg.Elements using (svg; g; rect'; path'; circle'; svgText)
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

record LineStyle : Set where
  constructor mkLineStyle
  field
    lsStroke    : String
    lsWidth     : Float
    lsFill      : String    -- for area below line ("none" for no fill)
    lsShowDots  : Bool
    lsDotRadius : Float

open LineStyle public

defaultLineStyle : LineStyle
defaultLineStyle = mkLineStyle "#3b82f6" 2.0 "none" true 3.0

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

  -- Zero-anchoring: ensure range always includes zero
  zeroMin : Float → Float
  zeroMin v = if v <ᵇ 0.0 then v else 0.0

  zeroMax : Float → Float
  zeroMax v = if 0.0 <ᵇ v then v else 0.0

------------------------------------------------------------------------
-- Path building
------------------------------------------------------------------------

private
  buildLinePath : Float → Float → Float → Float
               → Float → Float → Float → Float
               → List DataPoint → ℕ → String
  buildLinePath _ _ _ _ _ _ _ _ [] _ = ""
  buildLinePath px py w h minX maxX minY maxY (p ∷ ps) idx =
    let sx = scaleX minX maxX w px (dpX p)
        sy = scaleY minY maxY h py (dpY p)
        prefix = if idx ≡ᵇ 0 then "M " else " L "
    in prefix ++ showFloat sx ++ " " ++ showFloat sy
       ++ buildLinePath px py w h minX maxX minY maxY ps (suc idx)
    where
      open import Data.Nat using (_≡ᵇ_)

  -- Area path (line + close to bottom)
  buildAreaPath : Float → Float → Float → Float
                → Float → Float → Float → Float
                → List DataPoint → String
  buildAreaPath px py w h minX maxX minY maxY pts =
    let linePath = buildLinePath px py w h minX maxX minY maxY pts 0
        endY = py + h
        firstX = getFirstX pts
        lastX = getLastX pts
    in linePath
       ++ " L " ++ showFloat lastX ++ " " ++ showFloat endY
       ++ " L " ++ showFloat firstX ++ " " ++ showFloat endY
       ++ " Z"
    where
      getFirstX : List DataPoint → Float
      getFirstX [] = px
      getFirstX (p ∷ _) = scaleX minX maxX w px (dpX p)

      getLastX : List DataPoint → Float
      getLastX [] = px
      getLastX (p ∷ []) = scaleX minX maxX w px (dpX p)
      getLastX (_ ∷ ps) = getLastX ps

------------------------------------------------------------------------
-- Render dots
------------------------------------------------------------------------

private
  renderDots : ∀ {M Msg}
             → Float → Float → Float → Float
             → Float → Float → Float → Float
             → Float → String
             → List DataPoint → List (Node M Msg)
  renderDots _ _ _ _ _ _ _ _ _ _ [] = []
  renderDots px py w h minX maxX minY maxY radius color (p ∷ ps) =
    circle' ( cxF (scaleX minX maxX w px (dpX p))
            ∷ cyF (scaleY minY maxY h py (dpY p))
            ∷ rF radius
            ∷ fill_ color
            ∷ [] ) []
    ∷ renderDots px py w h minX maxX minY maxY radius color ps

------------------------------------------------------------------------
-- Simple Line Chart
------------------------------------------------------------------------

-- | Simple line chart with single series
simpleLineChart : ∀ {M Msg}
                → Float → Float → Float → Float  -- x, y, width, height
                → List DataPoint
                → LineStyle
                → Node M Msg
simpleLineChart px py w h [] sty = g [] []  -- empty data → empty chart
simpleLineChart px py w h points sty =
  let xs = extractX points
      ys = extractY points
      minX = findMin xs 1.0e10
      maxX = findMax xs (0.0 - 1.0e10)
      minY = zeroMin (findMin ys 1.0e10)
      maxY = zeroMax (findMax ys (0.0 - 1.0e10))
      linePath = buildLinePath px py w h minX maxX minY maxY points 0
  in g ( attr "class" "svg-line-chart" ∷ [] )
       ( -- Optional area fill
         (if lsFill sty ≡ˢ "none"
          then g [] []
          else path' ( d_ (buildAreaPath px py w h minX maxX minY maxY points)
                     ∷ fill_ (lsFill sty)
                     ∷ attr "opacity" "0.3"
                     ∷ [] ) [])
       -- Line path
       ∷ path' ( d_ linePath
               ∷ fill_ "none"
               ∷ stroke_ (lsStroke sty)
               ∷ strokeWidthF (lsWidth sty)
               ∷ attr "stroke-linecap" "round"
               ∷ attr "stroke-linejoin" "round"
               ∷ [] ) []
       -- Optional dots
       ∷ (if lsShowDots sty
          then g [] (renderDots px py w h minX maxX minY maxY
                      (lsDotRadius sty) (lsStroke sty) points)
          else g [] [])
       ∷ [] )
  where
    open import Data.String using (_≟_)
    open import Relation.Nullary using (yes; no)
    _≡ˢ_ : String → String → Bool
    s ≡ˢ t with s ≟ t
    ... | yes _ = true
    ... | no _ = false

------------------------------------------------------------------------
-- Multi-series Line Chart
------------------------------------------------------------------------

record LineSeries (M : Set) : Set where
  constructor mkLineSeries
  field
    seriesName  : String
    seriesColor : String
    seriesData  : M → List DataPoint

open LineSeries public

-- | Line chart with multiple series
lineChart : ∀ {M Msg}
          → Float → Float → Float → Float
          → Float                        -- stroke width
          → Bool                         -- show dots
          → List (LineSeries M)
          → Node M Msg
lineChart {M} {Msg} px py w h strokeW dots series =
  g ( attr "class" "svg-line-chart-multi" ∷ [] )
    ( renderSeries series )
  where
    renderOneSeries : LineSeries M → Node M Msg
    renderOneSeries s =
      -- For now, render with empty data (will be filled by model)
      -- In reactive mode, the data comes from the model
      g ( attr "class" ("series-" ++ seriesName s) ∷ [] ) []

    renderSeries : List (LineSeries M) → List (Node M Msg)
    renderSeries [] = []
    renderSeries (s ∷ ss) = renderOneSeries s ∷ renderSeries ss

------------------------------------------------------------------------
-- Line chart with reactive data
------------------------------------------------------------------------

-- | Line chart that reads data from model
-- Reactively scales data coordinates to SVG pixel space using min/max
-- from the full data set, same scaling logic as simpleLineChart.
reactiveLineChart : ∀ {M Msg}
                  → Float → Float → Float → Float
                  → (M → List DataPoint)
                  → LineStyle
                  → Node M Msg
reactiveLineChart {M} px py w h getData sty =
  g ( attr "class" "svg-line-chart-reactive" ∷ [] )
    ( -- Line path (reactively bound to model)
      path' ( attrBind "d" (stringBinding (λ m →
                let pts = getData m
                    xs  = extractX pts
                    ys  = extractY pts
                    mnX = findMin xs 1.0e10
                    mxX = findMax xs (0.0 - 1.0e10)
                    mnY = zeroMin (findMin ys 1.0e10)
                    mxY = zeroMax (findMax ys (0.0 - 1.0e10))
                in buildLinePath px py w h mnX mxX mnY mxY pts 0))
            ∷ fill_ "none"
            ∷ stroke_ (lsStroke sty)
            ∷ strokeWidthF (lsWidth sty)
            ∷ attr "stroke-linecap" "round"
            ∷ attr "stroke-linejoin" "round"
            ∷ [] ) []
    -- Optional area fill (reactively bound)
    ∷ (if lsFill sty ≡ˢ "none"
       then g [] []
       else path' ( attrBind "d" (stringBinding (λ m →
                      let pts = getData m
                          xs  = extractX pts
                          ys  = extractY pts
                          mnX = findMin xs 1.0e10
                          mxX = findMax xs (0.0 - 1.0e10)
                          mnY = zeroMin (findMin ys 1.0e10)
                          mxY = zeroMax (findMax ys (0.0 - 1.0e10))
                      in buildAreaPath px py w h mnX mxX mnY mxY pts))
                  ∷ fill_ (lsFill sty)
                  ∷ attr "opacity" "0.3"
                  ∷ [] ) [])
    -- Optional dots (foreach with scaled coordinates)
    ∷ (if lsShowDots sty
       then Agdelte.Reactive.Node.foreach getData (λ p idx →
              circle' ( attrBind "cx" (stringBinding (λ m →
                          let pts = getData m
                              xs  = extractX pts
                              mnX = findMin xs 1.0e10
                              mxX = findMax xs (0.0 - 1.0e10)
                          in showFloat (scaleX mnX mxX w px (dpX p))))
                      ∷ attrBind "cy" (stringBinding (λ m →
                          let pts = getData m
                              ys  = extractY pts
                              mnY = zeroMin (findMin ys 1.0e10)
                              mxY = zeroMax (findMax ys (0.0 - 1.0e10))
                          in showFloat (scaleY mnY mxY h py (dpY p))))
                      ∷ rF (lsDotRadius sty)
                      ∷ fill_ (lsStroke sty)
                      ∷ [] ) [])
       else g [] [])
    ∷ [] )
  where
    open import Agdelte.Reactive.Node using (foreach)
    open import Data.String using (_≟_)
    open import Relation.Nullary using (yes; no)
    _≡ˢ_ : String → String → Bool
    s ≡ˢ t with s ≟ t
    ... | yes _ = true
    ... | no _ = false

------------------------------------------------------------------------
-- Quick constructors
------------------------------------------------------------------------

-- | Simple blue line chart
blueLineChart : ∀ {M Msg}
              → Float → Float → Float → Float
              → List DataPoint
              → Node M Msg
blueLineChart px py w h pts =
  simpleLineChart px py w h pts defaultLineStyle

-- | Area chart (line with filled area)
areaLineChart : ∀ {M Msg}
              → Float → Float → Float → Float
              → List DataPoint
              → String                    -- fill color
              → Node M Msg
areaLineChart px py w h pts fillCol =
  simpleLineChart px py w h pts
    (mkLineStyle "#3b82f6" 2.0 fillCol true 3.0)

-- | Minimalist line (no dots)
minimalLineChart : ∀ {M Msg}
                 → Float → Float → Float → Float
                 → List DataPoint
                 → String                 -- color
                 → Node M Msg
minimalLineChart px py w h pts color =
  simpleLineChart px py w h pts
    (mkLineStyle color 2.0 "none" false 0.0)

------------------------------------------------------------------------
-- Line Chart with Gaps (Maybe Float for Y)
------------------------------------------------------------------------

-- | A data point with an optional Y value; nothing means a gap in the line.
GapDataPoint : Set
GapDataPoint = Float × Maybe Float

private
  extractGapX : List GapDataPoint → List Float
  extractGapX [] = []
  extractGapX ((vx , _) ∷ ps) = vx ∷ extractGapX ps

  extractGapY : List GapDataPoint → List Float
  extractGapY [] = []
  extractGapY ((_ , nothing) ∷ ps) = extractGapY ps
  extractGapY ((_ , just vy) ∷ ps) = vy ∷ extractGapY ps

  buildGapLinePath : Float → Float → Float → Float
                   → Float → Float → Float → Float
                   → List GapDataPoint → Bool → String
  buildGapLinePath _ _ _ _ _ _ _ _ [] _ = ""
  buildGapLinePath px py w h minX maxX minY maxY ((_ , nothing) ∷ ps) _ =
    -- Gap: next valid point will start a new M command
    buildGapLinePath px py w h minX maxX minY maxY ps false
  buildGapLinePath px py w h minX maxX minY maxY ((vx , just vy) ∷ ps) connected =
    let sx = scaleX minX maxX w px vx
        sy = scaleY minY maxY h py vy
        prefix = if connected then " L " else "M "
    in prefix ++ showFloat sx ++ " " ++ showFloat sy
       ++ buildGapLinePath px py w h minX maxX minY maxY ps true

-- | Line chart that accepts data points as (x, Maybe y).
--   When y = nothing, the line breaks (gap). When y = just v, the line continues.
lineChartWithGaps : ∀ {M Msg}
                  → Float → Float → Float → Float  -- x, y, width, height
                  → List GapDataPoint
                  → LineStyle
                  → Node M Msg
lineChartWithGaps px py w h points sty =
  let xs = extractGapX points
      ys = extractGapY points
      minX = findMin xs 1.0e10
      maxX = findMax xs (0.0 - 1.0e10)
      minY = zeroMin (findMin ys 1.0e10)
      maxY = zeroMax (findMax ys (0.0 - 1.0e10))
      linePath = buildGapLinePath px py w h minX maxX minY maxY points false
  in g ( attr "class" "svg-line-chart svg-line-chart--gaps" ∷ [] )
       ( -- Line path (no area fill for gap charts)
         path' ( d_ linePath
               ∷ fill_ "none"
               ∷ stroke_ (lsStroke sty)
               ∷ strokeWidthF (lsWidth sty)
               ∷ attr "stroke-linecap" "round"
               ∷ attr "stroke-linejoin" "round"
               ∷ [] ) []
       -- Optional dots (only for present values)
       ∷ (if lsShowDots sty
          then g [] (renderGapDots px py w h minX maxX minY maxY
                      (lsDotRadius sty) (lsStroke sty) points)
          else g [] [])
       ∷ [] )
  where
    renderGapDots : ∀ {M' Msg'}
                  → Float → Float → Float → Float
                  → Float → Float → Float → Float
                  → Float → String
                  → List GapDataPoint → List (Node M' Msg')
    renderGapDots _ _ _ _ _ _ _ _ _ _ [] = []
    renderGapDots px' py' w' h' mnX mxX mnY mxY r c ((_ , nothing) ∷ ps) =
      renderGapDots px' py' w' h' mnX mxX mnY mxY r c ps
    renderGapDots px' py' w' h' mnX mxX mnY mxY r c ((vx , just vy) ∷ ps) =
      circle' ( cxF (scaleX mnX mxX w' px' vx)
              ∷ cyF (scaleY mnY mxY h' py' vy)
              ∷ rF r
              ∷ fill_ c
              ∷ [] ) []
      ∷ renderGapDots px' py' w' h' mnX mxX mnY mxY r c ps
