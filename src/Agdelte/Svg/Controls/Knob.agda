{-# OPTIONS --without-K #-}

-- SvgKnob: rotary knob control
-- Circular dial that rotates to select value (like volume knobs)

module Agdelte.Svg.Controls.Knob where

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
-- Math constants
------------------------------------------------------------------------

private
  π : Float
  π = 3.14159265359

  -- Convert degrees to radians
  degToRad : Float → Float
  degToRad deg = deg * π ÷ 180.0

  -- Sine approximation (Taylor series)
  sin' : Float → Float
  sin' x = x - (x * x * x ÷ 6.0) + (x * x * x * x * x ÷ 120.0)

  -- Cosine approximation
  cos' : Float → Float
  cos' x = 1.0 - (x * x ÷ 2.0) + (x * x * x * x ÷ 24.0)

------------------------------------------------------------------------
-- Knob Style
------------------------------------------------------------------------

record KnobStyle : Set where
  constructor mkKnobStyle
  field
    knobRadius     : Float     -- outer circle radius
    knobColor      : String    -- main knob color
    knobBorder     : String    -- knob border
    indicatorColor : String    -- rotation indicator line
    indicatorWidth : Float     -- indicator thickness
    trackColor     : String    -- value arc track (optional)
    valueColor     : String    -- value arc fill
    arcWidth       : Float     -- value arc stroke width
    labelColor     : String    -- center label color
    labelSize      : String    -- label font size
    showValue      : Bool      -- show value in center

open KnobStyle public

-- Default metallic style
defaultKnobStyle : KnobStyle
defaultKnobStyle = mkKnobStyle
  40.0         -- radius
  "#f3f4f6"    -- light gray knob
  "#d1d5db"    -- gray border
  "#3b82f6"    -- blue indicator
  3.0          -- indicator width
  "#e5e7eb"    -- light track
  "#3b82f6"    -- blue arc
  4.0          -- arc width
  "#374151"    -- dark label
  "14px"       -- label size
  true         -- show value

-- Dark theme
darkKnobStyle : KnobStyle
darkKnobStyle = mkKnobStyle
  40.0
  "#374151"    -- dark knob
  "#4b5563"    -- gray border
  "#60a5fa"    -- light blue indicator
  3.0
  "#4b5563"
  "#60a5fa"
  4.0
  "#e5e7eb"    -- light label
  "14px"
  true

-- Minimal style (no arc)
minimalKnobStyle : KnobStyle
minimalKnobStyle = mkKnobStyle
  30.0
  "#ffffff"
  "#d1d5db"
  "#6366f1"    -- indigo
  2.0
  "transparent"
  "transparent"
  0.0
  "#374151"
  "12px"
  false

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

private
  clamp01 : Float → Float
  clamp01 v = if v ≤ᵇ 0.0 then 0.0 else if 1.0 ≤ᵇ v then 1.0 else v

  -- Knob rotates from -135° to +135° (270° range)
  valueToAngle : Float → Float
  valueToAngle ratio = (ratio - 0.5) * 270.0


------------------------------------------------------------------------
-- Knob
------------------------------------------------------------------------

svgKnob : ∀ {M Msg}
        → Float → Float       -- cx, cy (center)
        → Float               -- value (0-1)
        → KnobStyle
        → Node M Msg
svgKnob cx cy val sty =
  let ratio = clamp01 val
      r = knobRadius sty
      angle = valueToAngle ratio
      -- Indicator line endpoint
      indicatorR = r * 0.6
      indicatorRad = degToRad (angle - 90.0)
      indX = cx + indicatorR * cos' indicatorRad
      indY = cy + indicatorR * sin' indicatorRad
  in g ( attr "class" "svg-knob"
       ∷ attr "cursor" "pointer"
       ∷ [] )
       ( -- Value arc (behind knob)
         (if arcWidth sty ≤ᵇ 0.0
          then g [] []
          else g [] ( -- Track arc
                      elem "circle" ( attrCx cx
                                    ∷ attrCy cy
                                    ∷ rF (r + 8.0)
                                    ∷ fill_ "none"
                                    ∷ stroke_ (trackColor sty)
                                    ∷ strokeWidthF (arcWidth sty)
                                    ∷ attr "stroke-linecap" "round"
                                    ∷ attr "stroke-dasharray" (showFloat (2.0 * π * (r + 8.0) * 0.75))
                                    ∷ attr "stroke-dashoffset" (showFloat (2.0 * π * (r + 8.0) * 0.125))
                                    ∷ attr "transform" ("rotate(-135 " ++ showFloat cx ++ " " ++ showFloat cy ++ ")")
                                    ∷ [] ) []
                    -- Value arc
                    ∷ elem "circle" ( attrCx cx
                                    ∷ attrCy cy
                                    ∷ rF (r + 8.0)
                                    ∷ fill_ "none"
                                    ∷ stroke_ (valueColor sty)
                                    ∷ strokeWidthF (arcWidth sty)
                                    ∷ attr "stroke-linecap" "round"
                                    ∷ attr "stroke-dasharray" (showFloat (2.0 * π * (r + 8.0) * 0.75 * ratio)
                                                            ++ " " ++ showFloat (2.0 * π * (r + 8.0)))
                                    ∷ attr "transform" ("rotate(-135 " ++ showFloat cx ++ " " ++ showFloat cy ++ ")")
                                    ∷ [] ) []
                    ∷ [] ))
       -- Knob circle
       ∷ circle' ( attrCx cx
                 ∷ attrCy cy
                 ∷ rF r
                 ∷ fill_ (knobColor sty)
                 ∷ stroke_ (knobBorder sty)
                 ∷ strokeWidthF 2.0
                 ∷ [] ) []
       -- Indicator line
       ∷ elem "line" ( attr "x1" (showFloat cx)
                     ∷ attr "y1" (showFloat cy)
                     ∷ attr "x2" (showFloat indX)
                     ∷ attr "y2" (showFloat indY)
                     ∷ stroke_ (indicatorColor sty)
                     ∷ strokeWidthF (indicatorWidth sty)
                     ∷ attr "stroke-linecap" "round"
                     ∷ [] ) []
       -- Center dot
       ∷ circle' ( attrCx cx
                 ∷ attrCy cy
                 ∷ rF 3.0
                 ∷ fill_ (indicatorColor sty)
                 ∷ [] ) []
       -- Value label (optional)
       ∷ (if showValue sty
          then svgText ( attrX cx
                       ∷ attrY (cy + r + 20.0)
                       ∷ fill_ (labelColor sty)
                       ∷ attrFontSize (labelSize sty)
                       ∷ attrFontFamily "system-ui, sans-serif"
                       ∷ textAnchor_ "middle"
                       ∷ [] ) ( text (showFloat (ratio * 100.0) ++ "%") ∷ [] )
          else g [] [])
       ∷ [] )

------------------------------------------------------------------------
-- Knob with Label
------------------------------------------------------------------------

svgKnobLabeled : ∀ {M Msg}
               → Float → Float       -- cx, cy
               → Float               -- value (0-1)
               → String              -- label
               → KnobStyle
               → Node M Msg
svgKnobLabeled cx cy val lbl sty =
  let r = knobRadius sty
  in g ( attr "class" "svg-knob-labeled" ∷ [] )
       ( -- Label above
         svgText ( attrX cx
                 ∷ attrY (cy - r - 12.0)
                 ∷ fill_ (labelColor sty)
                 ∷ attrFontSize (labelSize sty)
                 ∷ attrFontFamily "system-ui, sans-serif"
                 ∷ textAnchor_ "middle"
                 ∷ [] ) ( text lbl ∷ [] )
       ∷ svgKnob cx cy val sty
       ∷ [] )

------------------------------------------------------------------------
-- Simple Knobs (default style)
------------------------------------------------------------------------

svgKnobSimple : ∀ {M Msg}
              → Float → Float → Float
              → Node M Msg
svgKnobSimple cx cy val =
  svgKnob cx cy val defaultKnobStyle

svgKnobSimpleLabeled : ∀ {M Msg}
                     → Float → Float → Float → String
                     → Node M Msg
svgKnobSimpleLabeled cx cy val lbl =
  svgKnobLabeled cx cy val lbl defaultKnobStyle

------------------------------------------------------------------------
-- Volume Knob (0-100 scale, shows dB-style marks)
------------------------------------------------------------------------

svgVolumeKnob : ∀ {M Msg}
              → Float → Float → Float  -- cx, cy, value (0-100)
              → Node M Msg
svgVolumeKnob cx cy val =
  svgKnobLabeled cx cy (val ÷ 100.0) "Volume" defaultKnobStyle
