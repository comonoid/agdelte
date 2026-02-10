{-# OPTIONS --without-K #-}

-- SvgRadioGroup: radio button group
-- Circular buttons with dot indicator

module Agdelte.Svg.Controls.RadioGroup where

open import Data.String using (String; _++_)
open import Data.Float using (Float; _+_; _-_; _*_)
open import Data.Float.Base using (_÷_)
open import Data.List using (List; []; _∷_; length)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Agdelte.Reactive.Node using (Node; Attr; elem; attr; on; text)
open import Agdelte.Svg.Elements using (g; circle'; svgText)
open import Agdelte.Svg.Attributes
  hiding (x_; y_)
  renaming (cxF to attrCx; cyF to attrCy; xF to attrX; yF to attrY;
            fontSize_ to attrFontSize; fontFamily_ to attrFontFamily)
open import Agdelte.Css.Show using (showFloat)

------------------------------------------------------------------------
-- Radio Style
------------------------------------------------------------------------

record RadioStyle : Set where
  constructor mkRadioStyle
  field
    outerRadius    : Float    -- outer circle radius
    innerRadius    : Float    -- inner dot radius (when selected)
    outerColor     : String   -- outer circle stroke
    outerFill      : String   -- outer circle fill
    innerColor     : String   -- inner dot color (selected)
    circleStroke   : Float    -- outer circle stroke width
    labelColor     : String   -- label text color
    labelSize      : String   -- label font size
    labelGap       : Float    -- gap between circle and label
    itemGap        : Float    -- gap between radio items

open RadioStyle public

-- Default style
defaultRadioStyle : RadioStyle
defaultRadioStyle = mkRadioStyle
  10.0         -- outer radius
  5.0          -- inner radius
  "#6b7280"    -- gray stroke
  "#ffffff"    -- white fill
  "#3b82f6"    -- blue dot
  2.0          -- stroke width
  "#374151"    -- dark label
  "14px"       -- label size
  8.0          -- label gap
  28.0         -- item gap

-- Blue theme (outer ring turns blue when selected)
blueRadioStyle : RadioStyle
blueRadioStyle = mkRadioStyle
  10.0
  5.0
  "#3b82f6"    -- blue stroke
  "#ffffff"
  "#3b82f6"    -- blue dot
  2.0
  "#374151"
  "14px"
  8.0
  28.0

-- Dark theme
darkRadioStyle : RadioStyle
darkRadioStyle = mkRadioStyle
  10.0
  5.0
  "#9ca3af"    -- light gray stroke
  "#1f2937"    -- dark fill
  "#60a5fa"    -- light blue dot
  2.0
  "#e5e7eb"    -- light label
  "14px"
  8.0
  28.0

------------------------------------------------------------------------
-- Single Radio Button
------------------------------------------------------------------------

svgRadio : ∀ {M Msg}
         → Float → Float      -- x, y (center of circle)
         → Bool               -- selected
         → RadioStyle
         → Msg                -- select message
         → Node M Msg
svgRadio cx cy selected sty msg =
  g ( attr "class" "svg-radio"
    ∷ attr "cursor" "pointer"
    ∷ on "click" msg
    ∷ [] )
    ( -- Outer circle
      circle' ( attrCx cx
              ∷ attrCy cy
              ∷ rF (outerRadius sty)
              ∷ fill_ (outerFill sty)
              ∷ stroke_ (outerColor sty)
              ∷ strokeWidthF (circleStroke sty)
              ∷ [] ) []
    -- Inner dot (only when selected)
    ∷ (if selected
       then circle' ( attrCx cx
                    ∷ attrCy cy
                    ∷ rF (innerRadius sty)
                    ∷ fill_ (innerColor sty)
                    ∷ attr "pointer-events" "none"
                    ∷ [] ) []
       else g [] [])
    ∷ [] )

------------------------------------------------------------------------
-- Radio with Label
------------------------------------------------------------------------

svgRadioLabeled : ∀ {M Msg}
                → Float → Float      -- x, y (center of circle)
                → Bool               -- selected
                → String             -- label
                → RadioStyle
                → Msg                -- select message
                → Node M Msg
svgRadioLabeled cx cy selected lbl sty msg =
  let labelX = cx + outerRadius sty + labelGap sty
  in g ( attr "class" "svg-radio-labeled"
       ∷ attr "cursor" "pointer"
       ∷ on "click" msg
       ∷ [] )
       ( svgRadio cx cy selected sty msg
       ∷ svgText ( attrX labelX
                 ∷ attrY cy
                 ∷ fill_ (labelColor sty)
                 ∷ attrFontSize (labelSize sty)
                 ∷ attrFontFamily "system-ui, sans-serif"
                 ∷ dominantBaseline_ "central"
                 ∷ attr "pointer-events" "none"
                 ∷ [] ) ( text lbl ∷ [] )
       ∷ [] )

------------------------------------------------------------------------
-- Radio Group (Vertical)
------------------------------------------------------------------------

-- Render vertical radio group
svgRadioGroupV : ∀ {M Msg}
               → Float → Float               -- x, y (top-left)
               → ℕ                           -- selected index
               → List (String × Msg)         -- (label, selectMsg) pairs
               → RadioStyle
               → Node M Msg
svgRadioGroupV {M} {Msg} px py selected items sty =
  g ( attr "class" "svg-radio-group-v" ∷ [] )
    (renderItems 0 py items)
  where
    renderItems : ℕ → Float → List (String × Msg) → List (Node M Msg)
    renderItems _ _ [] = []
    renderItems idx currentY ((lbl , msg) ∷ rest) =
      let isSelected = idx ≡ᵇ selected
          cx = px + outerRadius sty
      in svgRadioLabeled cx currentY isSelected lbl sty msg
         ∷ renderItems (suc idx) (currentY + itemGap sty) rest

------------------------------------------------------------------------
-- Radio Group (Horizontal)
------------------------------------------------------------------------

svgRadioGroupH : ∀ {M Msg}
               → Float → Float               -- x, y
               → ℕ                           -- selected index
               → List (String × Msg)         -- (label, selectMsg) pairs
               → Float                       -- item width (for spacing)
               → RadioStyle
               → Node M Msg
svgRadioGroupH {M} {Msg} px py selected items itemWidth sty =
  g ( attr "class" "svg-radio-group-h" ∷ [] )
    (renderItems 0 px items)
  where
    renderItems : ℕ → Float → List (String × Msg) → List (Node M Msg)
    renderItems _ _ [] = []
    renderItems idx currentX ((lbl , msg) ∷ rest) =
      let isSelected = idx ≡ᵇ selected
          cx = currentX + outerRadius sty
          cy = py
      in svgRadioLabeled cx cy isSelected lbl sty msg
         ∷ renderItems (suc idx) (currentX + itemWidth) rest

------------------------------------------------------------------------
-- Simple Radio Group (default style, vertical)
------------------------------------------------------------------------

svgRadioGroupSimple : ∀ {M Msg}
                    → Float → Float
                    → ℕ
                    → List (String × Msg)
                    → Node M Msg
svgRadioGroupSimple px py selected items =
  svgRadioGroupV px py selected items defaultRadioStyle

------------------------------------------------------------------------
-- Button-style Radio Group (segmented control)
------------------------------------------------------------------------

-- Segmented control style (like iOS)
record SegmentedStyle : Set where
  constructor mkSegmentedStyle
  field
    segHeight      : Float
    segPadding     : Float    -- horizontal padding per segment
    bgColor        : String   -- background
    selectedBg     : String   -- selected segment background
    textColor      : String   -- text color
    selectedText   : String   -- selected text color
    borderColor    : String   -- border
    borderRadius   : Float    -- corner radius
    segFontSize    : String

open SegmentedStyle public

defaultSegmentedStyle : SegmentedStyle
defaultSegmentedStyle = mkSegmentedStyle
  32.0
  16.0
  "#f3f4f6"    -- light gray bg
  "#3b82f6"    -- blue selected
  "#374151"    -- dark text
  "#ffffff"    -- white selected text
  "#d1d5db"    -- gray border
  6.0
  "14px"

-- Render segmented control
svgSegmentedControl : ∀ {M Msg}
                    → Float → Float           -- x, y
                    → ℕ                       -- selected index
                    → List (String × Msg)    -- (label, msg) pairs
                    → Float                  -- segment width
                    → SegmentedStyle
                    → Node M Msg
svgSegmentedControl {M} {Msg} px py selected items segW sty =
  let totalW = segW * Data.Float.Base.fromℕ (length items)
      h = segHeight sty
  in g ( attr "class" "svg-segmented" ∷ [] )
       ( -- Background
         elem "rect" ( attrX px
                     ∷ attrY py
                     ∷ widthF totalW
                     ∷ heightF h
                     ∷ fill_ (bgColor sty)
                     ∷ stroke_ (borderColor sty)
                     ∷ strokeWidthF 1.0
                     ∷ rxF (borderRadius sty)
                     ∷ ryF (borderRadius sty)
                     ∷ [] ) []
       ∷ renderSegments 0 px items )
  where
    renderSegments : ℕ → Float → List (String × Msg) → List (Node M Msg)
    renderSegments _ _ [] = []
    renderSegments idx currentX ((lbl , msg) ∷ rest) =
      let isSelected = idx ≡ᵇ selected
          textX = currentX + segW ÷ 2.0
          textY = py + segHeight sty ÷ 2.0
      in g ( attr "cursor" "pointer"
           ∷ on "click" msg
           ∷ [] )
           ( -- Selection highlight
             (if isSelected
              then elem "rect" ( attrX currentX
                               ∷ attrY py
                               ∷ widthF segW
                               ∷ heightF (segHeight sty)
                               ∷ fill_ (selectedBg sty)
                               ∷ rxF (borderRadius sty)
                               ∷ ryF (borderRadius sty)
                               ∷ attr "pointer-events" "none"
                               ∷ [] ) []
              else g [] [])
           -- Label
           ∷ svgText ( attrX textX
                     ∷ attrY textY
                     ∷ fill_ (if isSelected then selectedText sty else textColor sty)
                     ∷ attrFontSize (segFontSize sty)
                     ∷ attrFontFamily "system-ui, sans-serif"
                     ∷ textAnchor_ "middle"
                     ∷ dominantBaseline_ "central"
                     ∷ attr "pointer-events" "none"
                     ∷ [] ) ( text lbl ∷ [] )
           ∷ [] )
         ∷ renderSegments (suc idx) (currentX + segW) rest
