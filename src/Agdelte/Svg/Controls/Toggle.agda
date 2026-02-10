{-# OPTIONS --without-K #-}

-- SvgToggle: iOS-style toggle switch
-- Pill-shaped track with sliding circle thumb

module Agdelte.Svg.Controls.Toggle where

open import Data.String using (String; _++_)
open import Data.Float using (Float; _+_; _-_; _*_)
open import Data.Float.Base using (_÷_)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false; if_then_else_)

open import Agdelte.Reactive.Node using (Node; Attr; elem; attr; on; text)
open import Agdelte.Svg.Elements using (g; rect'; circle'; svgText)
open import Agdelte.Svg.Attributes
  hiding (x_; y_)
  renaming (xF to attrX; yF to attrY; cxF to attrCx; cyF to attrCy;
            fontSize_ to attrFontSize; fontFamily_ to attrFontFamily)
open import Agdelte.Css.Show using (showFloat)

------------------------------------------------------------------------
-- Toggle Style
------------------------------------------------------------------------

record ToggleStyle : Set where
  constructor mkToggleStyle
  field
    trackWidth     : Float    -- track width
    trackHeight    : Float    -- track height
    trackOff       : String   -- track color when off
    trackOn        : String   -- track color when on
    thumbColor     : String   -- thumb color
    thumbPadding   : Float    -- padding inside track
    labelColor     : String   -- label text color
    labelSize      : String   -- label font size
    labelGap       : Float    -- gap between toggle and label

open ToggleStyle public

-- Default iOS-like style
defaultToggleStyle : ToggleStyle
defaultToggleStyle = mkToggleStyle
  50.0         -- width
  28.0         -- height
  "#d1d5db"    -- gray off
  "#22c55e"    -- green on
  "#ffffff"    -- white thumb
  3.0          -- padding
  "#374151"    -- label color
  "14px"       -- label size
  10.0         -- label gap

-- Blue theme
blueToggleStyle : ToggleStyle
blueToggleStyle = mkToggleStyle
  50.0
  28.0
  "#d1d5db"
  "#3b82f6"    -- blue on
  "#ffffff"
  3.0
  "#374151"
  "14px"
  10.0

-- Dark theme
darkToggleStyle : ToggleStyle
darkToggleStyle = mkToggleStyle
  50.0
  28.0
  "#4b5563"    -- dark gray off
  "#60a5fa"    -- light blue on
  "#1f2937"    -- dark thumb
  3.0
  "#e5e7eb"    -- light label
  "14px"
  10.0

-- Small compact toggle
smallToggleStyle : ToggleStyle
smallToggleStyle = mkToggleStyle
  36.0         -- smaller width
  20.0         -- smaller height
  "#d1d5db"
  "#22c55e"
  "#ffffff"
  2.0          -- smaller padding
  "#374151"
  "12px"
  8.0

------------------------------------------------------------------------
-- Toggle (basic)
------------------------------------------------------------------------

svgToggle : ∀ {M Msg}
          → Float → Float       -- x, y position
          → Bool                -- on/off state
          → ToggleStyle
          → Msg                 -- toggle message
          → Node M Msg
svgToggle px py isOn sty msg =
  let w = trackWidth sty
      h = trackHeight sty
      pad = thumbPadding sty
      thumbR = (h - pad * 2.0) ÷ 2.0
      -- Thumb x position: left when off, right when on
      thumbX = if isOn
               then px + w - pad - thumbR
               else px + pad + thumbR
      thumbY = py + h ÷ 2.0
      trackColor = if isOn then trackOn sty else trackOff sty
  in g ( attr "class" "svg-toggle"
       ∷ attr "cursor" "pointer"
       ∷ on "click" msg
       ∷ [] )
       ( -- Track (pill shape using rx/ry = height/2)
         rect' ( attrX px
               ∷ attrY py
               ∷ widthF w
               ∷ heightF h
               ∷ fill_ trackColor
               ∷ rxF (h ÷ 2.0)
               ∷ ryF (h ÷ 2.0)
               ∷ [] ) []
       -- Thumb
       ∷ circle' ( attrCx thumbX
                 ∷ attrCy thumbY
                 ∷ rF thumbR
                 ∷ fill_ (thumbColor sty)
                 ∷ attr "pointer-events" "none"
                 ∷ [] ) []
       ∷ [] )

------------------------------------------------------------------------
-- Toggle with Label
------------------------------------------------------------------------

svgToggleLabeled : ∀ {M Msg}
                 → Float → Float      -- x, y position
                 → Bool               -- on/off state
                 → String             -- label text
                 → ToggleStyle
                 → Msg                -- toggle message
                 → Node M Msg
svgToggleLabeled px py isOn lbl sty msg =
  let labelX = px + trackWidth sty + labelGap sty
      labelY = py + trackHeight sty ÷ 2.0
  in g ( attr "class" "svg-toggle-labeled"
       ∷ attr "cursor" "pointer"
       ∷ on "click" msg
       ∷ [] )
       ( svgToggle px py isOn sty msg
       ∷ svgText ( attrX labelX
                 ∷ attrY labelY
                 ∷ fill_ (labelColor sty)
                 ∷ attrFontSize (labelSize sty)
                 ∷ attrFontFamily "system-ui, sans-serif"
                 ∷ dominantBaseline_ "central"
                 ∷ attr "pointer-events" "none"
                 ∷ [] ) ( text lbl ∷ [] )
       ∷ [] )

------------------------------------------------------------------------
-- Toggle with On/Off Labels
------------------------------------------------------------------------

svgToggleWithLabels : ∀ {M Msg}
                    → Float → Float      -- x, y position
                    → Bool               -- on/off state
                    → String → String    -- off label, on label
                    → ToggleStyle
                    → Msg                -- toggle message
                    → Node M Msg
svgToggleWithLabels px py isOn offLbl onLbl sty msg =
  let w = trackWidth sty
      h = trackHeight sty
      textY = py + h ÷ 2.0
      offX = px + w * 0.25
      onX = px + w * 0.75
      activeColor = "#ffffff"
      inactiveColor = "rgba(255,255,255,0.5)"
  in g ( attr "class" "svg-toggle-labels"
       ∷ attr "cursor" "pointer"
       ∷ on "click" msg
       ∷ [] )
       ( svgToggle px py isOn sty msg
       -- Off label (inside track, left)
       ∷ svgText ( attrX offX
                 ∷ attrY textY
                 ∷ fill_ (if isOn then inactiveColor else activeColor)
                 ∷ attrFontSize "10px"
                 ∷ attrFontFamily "system-ui, sans-serif"
                 ∷ textAnchor_ "middle"
                 ∷ dominantBaseline_ "central"
                 ∷ attr "pointer-events" "none"
                 ∷ [] ) ( text offLbl ∷ [] )
       -- On label (inside track, right)
       ∷ svgText ( attrX onX
                 ∷ attrY textY
                 ∷ fill_ (if isOn then activeColor else inactiveColor)
                 ∷ attrFontSize "10px"
                 ∷ attrFontFamily "system-ui, sans-serif"
                 ∷ textAnchor_ "middle"
                 ∷ dominantBaseline_ "central"
                 ∷ attr "pointer-events" "none"
                 ∷ [] ) ( text onLbl ∷ [] )
       ∷ [] )

------------------------------------------------------------------------
-- Simple Toggles (default style)
------------------------------------------------------------------------

svgToggleSimple : ∀ {M Msg}
                → Float → Float → Bool → Msg
                → Node M Msg
svgToggleSimple px py isOn msg =
  svgToggle px py isOn defaultToggleStyle msg

svgToggleSimpleLabeled : ∀ {M Msg}
                       → Float → Float → Bool → String → Msg
                       → Node M Msg
svgToggleSimpleLabeled px py isOn lbl msg =
  svgToggleLabeled px py isOn lbl defaultToggleStyle msg

------------------------------------------------------------------------
-- Power Toggle (with ON/OFF text)
------------------------------------------------------------------------

svgPowerToggle : ∀ {M Msg}
               → Float → Float → Bool → Msg
               → Node M Msg
svgPowerToggle px py isOn msg =
  svgToggleWithLabels px py isOn "OFF" "ON" defaultToggleStyle msg
