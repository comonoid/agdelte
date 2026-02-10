{-# OPTIONS --without-K #-}

-- SvgAxis: chart axes with tick marks and labels
-- X and Y axis for data visualization

module Agdelte.Svg.Controls.Axis where

open import Data.String using (String; _++_)
open import Data.Float using (Float; _+_; _-_; _*_)
open import Data.Float.Base using (_÷_; fromℕ)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc)

open import Agdelte.Reactive.Node using (Node; Attr; elem; attr; text)
open import Agdelte.Svg.Elements using (g; svgText)
open import Agdelte.Svg.Attributes
  hiding (x_; y_)
  renaming (xF to attrX; yF to attrY;
            fontSize_ to attrFontSize; fontFamily_ to attrFontFamily)
open import Agdelte.Css.Show using (showFloat)

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
      let ratio = fromℕ idx ÷ fromℕ (numTicks ∸ 1)
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
      where open import Data.Nat using (_∸_)

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
      let ratio = fromℕ idx ÷ fromℕ (numTicks ∸ 1)
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
      where open import Data.Nat using (_∸_)

------------------------------------------------------------------------
-- Simple Axes
------------------------------------------------------------------------

-- Numeric X axis (0 to max value)
svgAxisXNumeric : ∀ {M Msg}
                → Float → Float → Float → Float → ℕ
                → Node M Msg
svgAxisXNumeric px py w maxVal numTicks =
  svgAxisX px py w numTicks (λ r → showFloat (r * maxVal)) defaultAxisStyle

-- Numeric Y axis (0 to max value)
svgAxisYNumeric : ∀ {M Msg}
                → Float → Float → Float → Float → ℕ
                → Node M Msg
svgAxisYNumeric px py h maxVal numTicks =
  svgAxisY px py h numTicks (λ r → showFloat (r * maxVal)) defaultAxisStyle

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
      let ratio = fromℕ idx ÷ fromℕ (numLines ∸ 1)
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
      where open import Data.Nat using (_∸_)

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
      let ratio = fromℕ idx ÷ fromℕ (numLines ∸ 1)
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
      where open import Data.Nat using (_∸_)
