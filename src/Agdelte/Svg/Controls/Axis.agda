{-# OPTIONS --without-K #-}

-- SvgAxis: chart axes with tick marks and labels
-- X and Y axis for data visualization

module Agdelte.Svg.Controls.Axis where

open import Data.String using (String; _++_)
open import Data.Float using (Float; _+_; _-_; _*_)
open import Data.Float.Base using (_÷_; fromℕ)
  renaming (_≤ᵇ_ to _f≤ᵇ_; _<ᵇ_ to _f<ᵇ_)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _≤ᵇ_; _∸_)

open import Agdelte.Reactive.Node using (Node; Attr; elem; attr; text)
open import Agdelte.Svg.Elements using (g; svgText)
open import Agdelte.Svg.Attributes
  hiding (x_; y_)
  renaming (xF to attrX; yF to attrY;
            fontSize_ to attrFontSize; fontFamily_ to attrFontFamily)
open import Agdelte.Css.Show using (showFloat)

------------------------------------------------------------------------
-- Math primitives (JS backend)
------------------------------------------------------------------------

postulate
  floorF : Float → Float
  log10F : Float → Float
  powF   : Float → Float → Float

{-# COMPILE JS floorF = x => Math.floor(x) #-}
{-# COMPILE JS log10F = x => Math.log10(x) #-}
{-# COMPILE JS powF   = b => e => Math.pow(b, e) #-}

------------------------------------------------------------------------
-- Nice-numbers algorithm
------------------------------------------------------------------------

-- Compute a human-friendly tick interval for axis labelling.
-- Classic algorithm: round the raw interval to the nearest "nice" number
-- in the set {1, 2, 5, 10} × 10^k.

niceNum : Float → Float
niceNum rawInterval =
  let exponent    = floorF (log10F rawInterval)
      fraction    = rawInterval ÷ powF 10.0 exponent
      niceFrac    = if fraction f<ᵇ 1.5 then 1.0
                    else if fraction f<ᵇ 3.5 then 2.0
                    else if fraction f<ᵇ 7.5 then 5.0
                    else 10.0
  in niceFrac * powF 10.0 exponent

-- Compute nice min, nice max, and nice interval given data range and
-- desired number of ticks.
record NiceScale : Set where
  constructor mkNiceScale
  field
    niceMin      : Float
    niceMax      : Float
    niceInterval : Float

open NiceScale public

computeNiceScale : Float → Float → ℕ → NiceScale
computeNiceScale minVal maxVal numTicks =
  let range    = if (maxVal - minVal) f≤ᵇ 0.0 then 1.0 else maxVal - minVal
      rawInt   = range ÷ fromℕ (if numTicks ≤ᵇ 1 then 1 else numTicks ∸ 1)
      interval = niceNum rawInt
      nMin     = floorF (minVal ÷ interval) * interval
      nMax     = let candidate = nMin + interval * fromℕ numTicks
                 in if candidate f<ᵇ maxVal then candidate + interval else candidate
  in mkNiceScale nMin nMax interval

------------------------------------------------------------------------
-- Axis Style
------------------------------------------------------------------------

record AxisStyle : Set where
  constructor mkAxisStyle
  field
    lineColor     : String
    lineWidth     : Float
    tickLength    : Float
    tickWidth     : Float
    labelColor    : String
    labelSize     : String
    labelFamily   : String
    labelOffset   : Float    -- distance from axis

open AxisStyle public

defaultAxisStyle : AxisStyle
defaultAxisStyle = mkAxisStyle
  "#6b7280"    -- gray line
  1.0          -- line width
  6.0          -- tick length
  1.0          -- tick width
  "#374151"    -- label color
  "11px"       -- label size
  "system-ui, sans-serif"
  12.0         -- label offset

darkAxisStyle : AxisStyle
darkAxisStyle = mkAxisStyle
  "#9ca3af"
  1.0
  6.0
  1.0
  "#e5e7eb"
  "11px"
  "system-ui, sans-serif"
  12.0

------------------------------------------------------------------------
-- X Axis (bottom)
------------------------------------------------------------------------

svgAxisX : ∀ {M Msg}
         → Float → Float → Float   -- x, y, width
         → ℕ                       -- number of ticks
         → (Float → String)        -- label formatter (0-1 ratio → label)
         → AxisStyle
         → Node M Msg
svgAxisX {M} {Msg} px py w numTicks formatter sty =
  g ( attr "class" "svg-axis-x" ∷ [] )
    ( -- Main line
      elem "line" ( attr "x1" (showFloat px)
                  ∷ attr "y1" (showFloat py)
                  ∷ attr "x2" (showFloat (px + w))
                  ∷ attr "y2" (showFloat py)
                  ∷ stroke_ (lineColor sty)
                  ∷ strokeWidthF (lineWidth sty)
                  ∷ [] ) []
    ∷ renderTicks numTicks 0 )
  where
    renderTicks : ℕ → ℕ → List (Node M Msg)
    renderTicks zero _ = []
    renderTicks (suc remaining) idx =
      let ratio = if numTicks ≤ᵇ 1 then 0.0 else fromℕ idx ÷ fromℕ (numTicks ∸ 1)
          tickX = px + ratio * w
          tickY1 = py
          tickY2 = py + tickLength sty
          labelY = py + tickLength sty + labelOffset sty
      in g [] ( -- Tick mark
                elem "line" ( attr "x1" (showFloat tickX)
                            ∷ attr "y1" (showFloat tickY1)
                            ∷ attr "x2" (showFloat tickX)
                            ∷ attr "y2" (showFloat tickY2)
                            ∷ stroke_ (lineColor sty)
                            ∷ strokeWidthF (tickWidth sty)
                            ∷ [] ) []
              -- Label
              ∷ svgText ( attrX tickX
                        ∷ attrY labelY
                        ∷ fill_ (labelColor sty)
                        ∷ attrFontSize (labelSize sty)
                        ∷ attrFontFamily (labelFamily sty)
                        ∷ textAnchor_ "middle"
                        ∷ [] ) ( text (formatter ratio) ∷ [] )
              ∷ [] )
         ∷ renderTicks remaining (suc idx)

------------------------------------------------------------------------
-- Y Axis (left)
------------------------------------------------------------------------

svgAxisY : ∀ {M Msg}
         → Float → Float → Float   -- x, y, height
         → ℕ                       -- number of ticks
         → (Float → String)        -- label formatter
         → AxisStyle
         → Node M Msg
svgAxisY {M} {Msg} px py h numTicks formatter sty =
  g ( attr "class" "svg-axis-y" ∷ [] )
    ( -- Main line
      elem "line" ( attr "x1" (showFloat px)
                  ∷ attr "y1" (showFloat py)
                  ∷ attr "x2" (showFloat px)
                  ∷ attr "y2" (showFloat (py + h))
                  ∷ stroke_ (lineColor sty)
                  ∷ strokeWidthF (lineWidth sty)
                  ∷ [] ) []
    ∷ renderTicks numTicks 0 )
  where
    renderTicks : ℕ → ℕ → List (Node M Msg)
    renderTicks zero _ = []
    renderTicks (suc remaining) idx =
      let ratio = if numTicks ≤ᵇ 1 then 0.0 else fromℕ idx ÷ fromℕ (numTicks ∸ 1)
          -- Y axis: 0 at bottom, 1 at top (invert)
          tickY = py + h - ratio * h
          tickX1 = px - tickLength sty
          tickX2 = px
          labelX = px - tickLength sty - labelOffset sty
      in g [] ( -- Tick mark
                elem "line" ( attr "x1" (showFloat tickX1)
                            ∷ attr "y1" (showFloat tickY)
                            ∷ attr "x2" (showFloat tickX2)
                            ∷ attr "y2" (showFloat tickY)
                            ∷ stroke_ (lineColor sty)
                            ∷ strokeWidthF (tickWidth sty)
                            ∷ [] ) []
              -- Label
              ∷ svgText ( attrX labelX
                        ∷ attrY tickY
                        ∷ fill_ (labelColor sty)
                        ∷ attrFontSize (labelSize sty)
                        ∷ attrFontFamily (labelFamily sty)
                        ∷ textAnchor_ "end"
                        ∷ dominantBaseline_ "central"
                        ∷ [] ) ( text (formatter ratio) ∷ [] )
              ∷ [] )
         ∷ renderTicks remaining (suc idx)

------------------------------------------------------------------------
-- Simple Axes
------------------------------------------------------------------------

-- Numeric X axis with nice-number tick values
-- Takes min and max data values; computes human-friendly ticks.
svgAxisXNumeric : ∀ {M Msg}
                → Float → Float → Float → Float → Float → ℕ
                → Node M Msg
svgAxisXNumeric px py w minVal maxVal numTicks =
  let ns = computeNiceScale minVal maxVal numTicks
  in svgAxisX px py w numTicks
       (λ r → showFloat (niceMin ns + r * (niceMax ns - niceMin ns)))
       defaultAxisStyle

-- Numeric Y axis with nice-number tick values
svgAxisYNumeric : ∀ {M Msg}
                → Float → Float → Float → Float → Float → ℕ
                → Node M Msg
svgAxisYNumeric px py h minVal maxVal numTicks =
  let ns = computeNiceScale minVal maxVal numTicks
  in svgAxisY px py h numTicks
       (λ r → showFloat (niceMin ns + r * (niceMax ns - niceMin ns)))
       defaultAxisStyle

-- Percentage axis (0-100%)
svgAxisXPercent : ∀ {M Msg}
                → Float → Float → Float → ℕ
                → Node M Msg
svgAxisXPercent px py w numTicks =
  svgAxisX px py w numTicks (λ r → showFloat (r * 100.0) ++ "%") defaultAxisStyle

svgAxisYPercent : ∀ {M Msg}
                → Float → Float → Float → ℕ
                → Node M Msg
svgAxisYPercent px py h numTicks =
  svgAxisY px py h numTicks (λ r → showFloat (r * 100.0) ++ "%") defaultAxisStyle

------------------------------------------------------------------------
-- Grid Lines
------------------------------------------------------------------------

svgGridLinesX : ∀ {M Msg}
              → Float → Float → Float → Float  -- x, y, width, height
              → ℕ                              -- number of lines
              → String                         -- color
              → Node M Msg
svgGridLinesX {M} {Msg} px py w h numLines color =
  g ( attr "class" "svg-grid-x" ∷ [] )
    (renderLines numLines 0)
  where
    renderLines : ℕ → ℕ → List (Node M Msg)
    renderLines zero _ = []
    renderLines (suc remaining) idx =
      let ratio = if numLines ≤ᵇ 1 then 0.0 else fromℕ idx ÷ fromℕ (numLines ∸ 1)
          lineX = px + ratio * w
      in elem "line" ( attr "x1" (showFloat lineX)
                     ∷ attr "y1" (showFloat py)
                     ∷ attr "x2" (showFloat lineX)
                     ∷ attr "y2" (showFloat (py + h))
                     ∷ stroke_ color
                     ∷ strokeWidthF 0.5
                     ∷ attr "stroke-dasharray" "2,2"
                     ∷ [] ) []
         ∷ renderLines remaining (suc idx)

svgGridLinesY : ∀ {M Msg}
              → Float → Float → Float → Float
              → ℕ
              → String
              → Node M Msg
svgGridLinesY {M} {Msg} px py w h numLines color =
  g ( attr "class" "svg-grid-y" ∷ [] )
    (renderLines numLines 0)
  where
    renderLines : ℕ → ℕ → List (Node M Msg)
    renderLines zero _ = []
    renderLines (suc remaining) idx =
      let ratio = if numLines ≤ᵇ 1 then 0.0 else fromℕ idx ÷ fromℕ (numLines ∸ 1)
          lineY = py + ratio * h
      in elem "line" ( attr "x1" (showFloat px)
                     ∷ attr "y1" (showFloat lineY)
                     ∷ attr "x2" (showFloat (px + w))
                     ∷ attr "y2" (showFloat lineY)
                     ∷ stroke_ color
                     ∷ strokeWidthF 0.5
                     ∷ attr "stroke-dasharray" "2,2"
                     ∷ [] ) []
         ∷ renderLines remaining (suc idx)
