{-# OPTIONS --without-K #-}

-- SvgGauge: speedometer-style gauge indicator
-- Semi-circular arc with needle indicator

module Agdelte.Svg.Controls.Gauge where

open import Data.String using (String; _++_)
open import Data.Float using (Float; _+_; _-_; _*_)
open import Data.Float.Base using (_÷_; _≤ᵇ_)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false; if_then_else_)

open import Agdelte.Reactive.Node using (Node; Attr; elem; attr; on; text)
open import Agdelte.Svg.Elements using (g; circle'; svgText)
open import Agdelte.Svg.Attributes
  hiding (x_; y_)
  renaming (xF to attrX; yF to attrY; cxF to attrCx; cyF to attrCy;
            fontSize_ to attrFontSize; fontFamily_ to attrFontFamily)
open import Agdelte.Css.Show using (showFloat)

------------------------------------------------------------------------
-- Math
------------------------------------------------------------------------

private
  π : Float
  π = 3.14159265359

  degToRad : Float → Float
  degToRad d = d * π ÷ 180.0

  sin' : Float → Float
  sin' x = x - (x * x * x ÷ 6.0) + (x * x * x * x * x ÷ 120.0)

  cos' : Float → Float
  cos' x = 1.0 - (x * x ÷ 2.0) + (x * x * x * x ÷ 24.0)

  clamp01 : Float → Float
  clamp01 v = if v ≤ᵇ 0.0 then 0.0 else if 1.0 ≤ᵇ v then 1.0 else v

------------------------------------------------------------------------
-- Gauge Style
------------------------------------------------------------------------

record GaugeStyle : Set where
  constructor mkGaugeStyle
  field
    gaugeRadius    : Float
    trackColor     : String
    valueColor     : String
    needleColor    : String
    centerColor    : String
    arcWidth       : Float
    needleWidth    : Float
    labelColor     : String
    labelSize      : String
    showValue      : Bool

open GaugeStyle public

defaultGaugeStyle : GaugeStyle
defaultGaugeStyle = mkGaugeStyle
  60.0         -- radius
  "#e5e7eb"    -- light track
  "#3b82f6"    -- blue value
  "#1f2937"    -- dark needle
  "#6b7280"    -- gray center
  8.0          -- arc width
  3.0          -- needle width
  "#374151"    -- label color
  "20px"       -- label size
  true         -- show value

darkGaugeStyle : GaugeStyle
darkGaugeStyle = mkGaugeStyle
  60.0
  "#4b5563"
  "#60a5fa"
  "#f3f4f6"
  "#9ca3af"
  8.0
  3.0
  "#e5e7eb"
  "20px"
  true

------------------------------------------------------------------------
-- Gauge
------------------------------------------------------------------------

svgGauge : ∀ {M Msg}
         → Float → Float       -- cx, cy
         → Float               -- value (0-1)
         → GaugeStyle
         → Node M Msg
svgGauge cx cy val sty =
  let ratio = clamp01 val
      r = gaugeRadius sty
      -- Gauge arc from -135° to +135° (270° range)
      startAngle = -135.0
      angleRange = 270.0
      currentAngle = startAngle + ratio * angleRange
      -- Needle endpoint
      needleR = r * 0.75
      needleRad = degToRad currentAngle
      needleX = cx + needleR * cos' needleRad
      needleY = cy + needleR * sin' needleRad
      -- Arc calculations
      circumference = 2.0 * π * r
      arcLen = circumference * 0.75  -- 270° = 75% of circle
      valueLen = arcLen * ratio
  in g ( attr "class" "svg-gauge" ∷ [] )
       ( -- Track arc
         circle' ( attrCx cx
                 ∷ attrCy cy
                 ∷ rF r
                 ∷ fill_ "none"
                 ∷ stroke_ (trackColor sty)
                 ∷ strokeWidthF (arcWidth sty)
                 ∷ attr "stroke-linecap" "round"
                 ∷ attr "stroke-dasharray" (showFloat arcLen ++ " " ++ showFloat circumference)
                 ∷ attr "transform" ("rotate(135 " ++ showFloat cx ++ " " ++ showFloat cy ++ ")")
                 ∷ [] ) []
       -- Value arc
       ∷ circle' ( attrCx cx
                 ∷ attrCy cy
                 ∷ rF r
                 ∷ fill_ "none"
                 ∷ stroke_ (valueColor sty)
                 ∷ strokeWidthF (arcWidth sty)
                 ∷ attr "stroke-linecap" "round"
                 ∷ attr "stroke-dasharray" (showFloat valueLen ++ " " ++ showFloat circumference)
                 ∷ attr "transform" ("rotate(135 " ++ showFloat cx ++ " " ++ showFloat cy ++ ")")
                 ∷ [] ) []
       -- Needle
       ∷ elem "line" ( attr "x1" (showFloat cx)
                     ∷ attr "y1" (showFloat cy)
                     ∷ attr "x2" (showFloat needleX)
                     ∷ attr "y2" (showFloat needleY)
                     ∷ stroke_ (needleColor sty)
                     ∷ strokeWidthF (needleWidth sty)
                     ∷ attr "stroke-linecap" "round"
                     ∷ [] ) []
       -- Center circle
       ∷ circle' ( attrCx cx
                 ∷ attrCy cy
                 ∷ rF 6.0
                 ∷ fill_ (centerColor sty)
                 ∷ [] ) []
       -- Value label
       ∷ (if showValue sty
          then svgText ( attrX cx
                       ∷ attrY (cy + r * 0.4)
                       ∷ fill_ (labelColor sty)
                       ∷ attrFontSize (labelSize sty)
                       ∷ attrFontFamily "system-ui, sans-serif"
                       ∷ textAnchor_ "middle"
                       ∷ attr "font-weight" "600"
                       ∷ [] ) ( text (showFloat (ratio * 100.0)) ∷ [] )
          else g [] [])
       ∷ [] )

------------------------------------------------------------------------
-- Simple Gauges
------------------------------------------------------------------------

svgGaugeSimple : ∀ {M Msg} → Float → Float → Float → Node M Msg
svgGaugeSimple cx cy val = svgGauge cx cy val defaultGaugeStyle

-- Speed gauge (0-200)
svgSpeedGauge : ∀ {M Msg} → Float → Float → Float → Node M Msg
svgSpeedGauge cx cy speed = svgGauge cx cy (speed ÷ 200.0) defaultGaugeStyle

-- Temperature gauge (0-100°C)
svgTempGauge : ∀ {M Msg} → Float → Float → Float → Node M Msg
svgTempGauge cx cy temp = svgGauge cx cy (temp ÷ 100.0) defaultGaugeStyle
