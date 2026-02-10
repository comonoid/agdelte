{-# OPTIONS --without-K #-}

-- SvgCheckbox: SVG checkbox with checkmark animation
-- Square box with check mark indicator

module Agdelte.Svg.Controls.Checkbox where

open import Data.String using (String; _++_)
open import Data.Float using (Float; _+_; _-_; _*_)
open import Data.Float.Base using (_÷_)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false; if_then_else_)

open import Agdelte.Reactive.Node using (Node; Attr; elem; attr; on; text)
open import Agdelte.Svg.Elements using (g; rect'; svgText)
open import Agdelte.Svg.Attributes
  hiding (x_; y_)
  renaming (xF to attrX; yF to attrY; fontSize_ to attrFontSize; fontFamily_ to attrFontFamily)
open import Agdelte.Css.Show using (showFloat)

------------------------------------------------------------------------
-- Checkbox Style
------------------------------------------------------------------------

record CheckboxStyle : Set where
  constructor mkCheckboxStyle
  field
    boxSize       : Float     -- box width/height
    boxColor      : String    -- unchecked background
    checkedColor  : String    -- checked background
    borderColor   : String    -- border color
    borderWidth   : Float     -- border stroke width
    checkColor    : String    -- checkmark color
    checkStroke   : Float     -- checkmark stroke width
    cornerRadius  : Float     -- box corner radius
    labelColor    : String    -- label text color
    labelSize     : String    -- label font size
    labelGap      : Float     -- gap between box and label

open CheckboxStyle public

-- Default style (blue theme)
defaultCheckboxStyle : CheckboxStyle
defaultCheckboxStyle = mkCheckboxStyle
  20.0         -- box size
  "#ffffff"    -- white unchecked
  "#3b82f6"    -- blue checked
  "#d1d5db"    -- gray border
  2.0          -- border width
  "#ffffff"    -- white check
  2.5          -- check stroke
  4.0          -- corner radius
  "#374151"    -- dark gray label
  "14px"       -- label size
  8.0          -- label gap

-- Dark theme
darkCheckboxStyle : CheckboxStyle
darkCheckboxStyle = mkCheckboxStyle
  20.0
  "#374151"    -- dark gray unchecked
  "#60a5fa"    -- light blue checked
  "#6b7280"    -- gray border
  2.0
  "#1f2937"    -- dark check
  2.5
  4.0
  "#e5e7eb"    -- light label
  "14px"
  8.0

-- Green success theme
greenCheckboxStyle : CheckboxStyle
greenCheckboxStyle = mkCheckboxStyle
  20.0
  "#ffffff"
  "#22c55e"    -- green checked
  "#d1d5db"
  2.0
  "#ffffff"
  2.5
  4.0
  "#374151"
  "14px"
  8.0

------------------------------------------------------------------------
-- Checkmark Path (relative to box)
------------------------------------------------------------------------

-- Generate checkmark path centered in box
-- Path: small polyline from ~25% to ~45% to ~75%
checkmarkPath : Float → Float → Float → String
checkmarkPath bx by size =
  let x1 = bx + size * 0.2
      y1 = by + size * 0.5
      x2 = bx + size * 0.4
      y2 = by + size * 0.7
      x3 = bx + size * 0.8
      y3 = by + size * 0.3
  in "M " ++ showFloat x1 ++ " " ++ showFloat y1
     ++ " L " ++ showFloat x2 ++ " " ++ showFloat y2
     ++ " L " ++ showFloat x3 ++ " " ++ showFloat y3

------------------------------------------------------------------------
-- Checkbox (without label)
------------------------------------------------------------------------

svgCheckbox : ∀ {M Msg}
            → Float → Float        -- x, y position
            → Bool                 -- checked state
            → CheckboxStyle
            → Msg                  -- toggle message
            → Node M Msg
svgCheckbox px py checked sty msg =
  let size = boxSize sty
      bg = if checked then checkedColor sty else boxColor sty
  in g ( attr "class" "svg-checkbox"
       ∷ attr "cursor" "pointer"
       ∷ [] )
       ( -- Box
         rect' ( attrX px
               ∷ attrY py
               ∷ widthF size
               ∷ heightF size
               ∷ fill_ bg
               ∷ stroke_ (borderColor sty)
               ∷ strokeWidthF (borderWidth sty)
               ∷ rxF (cornerRadius sty)
               ∷ ryF (cornerRadius sty)
               ∷ on "click" msg
               ∷ [] ) []
       -- Checkmark (only when checked)
       ∷ (if checked
          then elem "path" ( d_ (checkmarkPath px py size)
                           ∷ fill_ "none"
                           ∷ stroke_ (checkColor sty)
                           ∷ strokeWidthF (checkStroke sty)
                           ∷ attr "stroke-linecap" "round"
                           ∷ attr "stroke-linejoin" "round"
                           ∷ attr "pointer-events" "none"
                           ∷ [] ) []
          else g [] [])
       ∷ [] )

------------------------------------------------------------------------
-- Checkbox with Label
------------------------------------------------------------------------

svgCheckboxLabeled : ∀ {M Msg}
                   → Float → Float     -- x, y position
                   → Bool              -- checked state
                   → String            -- label text
                   → CheckboxStyle
                   → Msg               -- toggle message
                   → Node M Msg
svgCheckboxLabeled px py checked lbl sty msg =
  let size = boxSize sty
      labelX = px + size + labelGap sty
      labelY = py + size ÷ 2.0
  in g ( attr "class" "svg-checkbox-labeled"
       ∷ attr "cursor" "pointer"
       ∷ on "click" msg
       ∷ [] )
       ( svgCheckbox px py checked sty msg
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
-- Simple Checkbox (default style)
------------------------------------------------------------------------

svgCheckboxSimple : ∀ {M Msg}
                  → Float → Float → Bool → Msg
                  → Node M Msg
svgCheckboxSimple px py checked msg =
  svgCheckbox px py checked defaultCheckboxStyle msg

svgCheckboxSimpleLabeled : ∀ {M Msg}
                         → Float → Float → Bool → String → Msg
                         → Node M Msg
svgCheckboxSimpleLabeled px py checked lbl msg =
  svgCheckboxLabeled px py checked lbl defaultCheckboxStyle msg

------------------------------------------------------------------------
-- Indeterminate Checkbox (for tree views)
------------------------------------------------------------------------

-- Checkbox with optional indeterminate state
data CheckState : Set where
  Unchecked     : CheckState
  Checked       : CheckState
  Indeterminate : CheckState

-- Minus sign path for indeterminate
indeterminatePath : Float → Float → Float → String
indeterminatePath bx by size =
  let x1 = bx + size * 0.25
      x2 = bx + size * 0.75
      y  = by + size * 0.5
  in "M " ++ showFloat x1 ++ " " ++ showFloat y
     ++ " L " ++ showFloat x2 ++ " " ++ showFloat y

svgCheckboxTriState : ∀ {M Msg}
                    → Float → Float
                    → CheckState
                    → CheckboxStyle
                    → Msg
                    → Node M Msg
svgCheckboxTriState {M} {Msg} px py state sty msg =
  let size = boxSize sty
      bg = getBg state
      icon = getIcon state
  in g ( attr "class" "svg-checkbox-tristate"
       ∷ attr "cursor" "pointer"
       ∷ [] )
       ( rect' ( attrX px
               ∷ attrY py
               ∷ widthF size
               ∷ heightF size
               ∷ fill_ bg
               ∷ stroke_ (borderColor sty)
               ∷ strokeWidthF (borderWidth sty)
               ∷ rxF (cornerRadius sty)
               ∷ ryF (cornerRadius sty)
               ∷ on "click" msg
               ∷ [] ) []
       ∷ icon
       ∷ [] )
  where
    getBg : CheckState → String
    getBg Unchecked = boxColor sty
    getBg Checked = checkedColor sty
    getBg Indeterminate = checkedColor sty

    getIcon : CheckState → Node M Msg
    getIcon Unchecked = g [] []
    getIcon Checked = elem "path"
      ( d_ (checkmarkPath px py (boxSize sty))
      ∷ fill_ "none"
      ∷ stroke_ (checkColor sty)
      ∷ strokeWidthF (checkStroke sty)
      ∷ attr "stroke-linecap" "round"
      ∷ attr "stroke-linejoin" "round"
      ∷ attr "pointer-events" "none"
      ∷ [] ) []
    getIcon Indeterminate = elem "path"
      ( d_ (indeterminatePath px py (boxSize sty))
      ∷ fill_ "none"
      ∷ stroke_ (checkColor sty)
      ∷ strokeWidthF (checkStroke sty)
      ∷ attr "stroke-linecap" "round"
      ∷ attr "pointer-events" "none"
      ∷ [] ) []
