{-# OPTIONS --without-K #-}

-- SvgTooltip: positioned tooltip/popover
-- Text bubble with arrow pointing to anchor

module Agdelte.Svg.Controls.Tooltip where

open import Data.String using (String; _++_)
open import Data.Float using (Float; _+_; _-_; _*_)
open import Data.Float.Base using (_÷_)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false; if_then_else_)

open import Agdelte.Reactive.Node using (Node; Attr; elem; attr; on; text)
open import Agdelte.Svg.Elements using (g; rect'; svgText)
open import Agdelte.Svg.Attributes
  hiding (x_; y_)
  renaming (xF to attrX; yF to attrY;
            fontSize_ to attrFontSize; fontFamily_ to attrFontFamily)
open import Agdelte.Css.Show using (showFloat)

------------------------------------------------------------------------
-- Tooltip Position
------------------------------------------------------------------------

data TooltipPosition : Set where
  Top    : TooltipPosition
  Bottom : TooltipPosition
  Left   : TooltipPosition
  Right  : TooltipPosition

------------------------------------------------------------------------
-- Tooltip Style
------------------------------------------------------------------------

record TooltipStyle : Set where
  constructor mkTooltipStyle
  field
    bgColor      : String    -- background color
    textColor    : String    -- text color
    borderColor  : String    -- border (optional)
    borderWidth  : Float     -- border width
    ttPadding    : Float     -- internal padding
    cornerRadius : Float     -- rounded corners
    arrowSize    : Float     -- arrow triangle size
    ttFontSize   : String    -- font size
    ttFontFamily : String    -- font family
    maxWidth     : Float     -- max width before wrap

open TooltipStyle public

-- Default dark tooltip
defaultTooltipStyle : TooltipStyle
defaultTooltipStyle = mkTooltipStyle
  "#1f2937"            -- dark bg
  "#ffffff"            -- white text
  "transparent"        -- no border
  0.0
  8.0                  -- padding
  4.0                  -- corner radius
  6.0                  -- arrow size
  "12px"
  "system-ui, sans-serif"
  200.0                -- max width

-- Light tooltip
lightTooltipStyle : TooltipStyle
lightTooltipStyle = mkTooltipStyle
  "#ffffff"
  "#1f2937"
  "#e5e7eb"            -- gray border
  1.0
  8.0
  4.0
  6.0
  "12px"
  "system-ui, sans-serif"
  200.0

-- Info tooltip (blue)
infoTooltipStyle : TooltipStyle
infoTooltipStyle = mkTooltipStyle
  "#dbeafe"            -- light blue bg
  "#1e40af"            -- dark blue text
  "#3b82f6"            -- blue border
  1.0
  8.0
  4.0
  6.0
  "12px"
  "system-ui, sans-serif"
  200.0

-- Warning tooltip (yellow)
warningTooltipStyle : TooltipStyle
warningTooltipStyle = mkTooltipStyle
  "#fef3c7"
  "#92400e"
  "#f59e0b"
  1.0
  8.0
  4.0
  6.0
  "12px"
  "system-ui, sans-serif"
  200.0

-- Error tooltip (red)
errorTooltipStyle : TooltipStyle
errorTooltipStyle = mkTooltipStyle
  "#fee2e2"
  "#991b1b"
  "#ef4444"
  1.0
  8.0
  4.0
  6.0
  "12px"
  "system-ui, sans-serif"
  200.0

------------------------------------------------------------------------
-- Arrow Path Generation
------------------------------------------------------------------------

private
  -- Generate arrow path based on position
  arrowPath : TooltipPosition → Float → Float → Float → Float → Float → String
  arrowPath Top tipX tipY w h size =
    -- Arrow pointing down (tooltip is above)
    let ax = tipX
        ay = tipY + h + size
        lx = tipX - size
        rx = tipX + size
    in "M " ++ showFloat lx ++ " " ++ showFloat (tipY + h)
       ++ " L " ++ showFloat ax ++ " " ++ showFloat ay
       ++ " L " ++ showFloat rx ++ " " ++ showFloat (tipY + h)
       ++ " Z"

  arrowPath Bottom tipX tipY w h size =
    -- Arrow pointing up
    let ax = tipX
        ay = tipY - size
        lx = tipX - size
        rx = tipX + size
    in "M " ++ showFloat lx ++ " " ++ showFloat tipY
       ++ " L " ++ showFloat ax ++ " " ++ showFloat ay
       ++ " L " ++ showFloat rx ++ " " ++ showFloat tipY
       ++ " Z"

  arrowPath Left tipX tipY w h size =
    -- Arrow pointing right
    let ax = tipX + w + size
        ay = tipY + h ÷ 2.0
        ty = tipY + h ÷ 2.0 - size
        by = tipY + h ÷ 2.0 + size
    in "M " ++ showFloat (tipX + w) ++ " " ++ showFloat ty
       ++ " L " ++ showFloat ax ++ " " ++ showFloat ay
       ++ " L " ++ showFloat (tipX + w) ++ " " ++ showFloat by
       ++ " Z"

  arrowPath Right tipX tipY w h size =
    -- Arrow pointing left
    let ax = tipX - size
        ay = tipY + h ÷ 2.0
        ty = tipY + h ÷ 2.0 - size
        by = tipY + h ÷ 2.0 + size
    in "M " ++ showFloat tipX ++ " " ++ showFloat ty
       ++ " L " ++ showFloat ax ++ " " ++ showFloat ay
       ++ " L " ++ showFloat tipX ++ " " ++ showFloat by
       ++ " Z"

------------------------------------------------------------------------
-- Tooltip
------------------------------------------------------------------------

-- Render tooltip at anchor point with given position
svgTooltip : ∀ {M Msg}
           → Float → Float          -- anchor x, y (point tooltip points to)
           → Float → Float          -- estimated width, height of content
           → String                 -- tooltip text
           → TooltipPosition
           → TooltipStyle
           → Node M Msg
svgTooltip anchorX anchorY w h txt pos sty =
  let pad = ttPadding sty
      arr = arrowSize sty
      totalW = w + pad * 2.0
      totalH = h + pad * 2.0
      -- Calculate tooltip box position based on position
      boxX = calcBoxX pos anchorX totalW arr
      boxY = calcBoxY pos anchorY totalH arr
      textX = boxX + pad
      textY = boxY + pad + h ÷ 2.0
  in g ( attr "class" "svg-tooltip"
       ∷ attr "pointer-events" "none"
       ∷ [] )
       ( -- Background rect
         rect' ( attrX boxX
               ∷ attrY boxY
               ∷ widthF totalW
               ∷ heightF totalH
               ∷ fill_ (bgColor sty)
               ∷ stroke_ (borderColor sty)
               ∷ strokeWidthF (borderWidth sty)
               ∷ rxF (cornerRadius sty)
               ∷ ryF (cornerRadius sty)
               ∷ [] ) []
       -- Arrow
       ∷ elem "path" ( d_ (arrowPath pos boxX boxY totalW totalH arr)
                     ∷ fill_ (bgColor sty)
                     ∷ stroke_ (borderColor sty)
                     ∷ strokeWidthF (borderWidth sty)
                     ∷ [] ) []
       -- Text
       ∷ svgText ( attrX (boxX + totalW ÷ 2.0)
                 ∷ attrY (boxY + totalH ÷ 2.0)
                 ∷ fill_ (textColor sty)
                 ∷ attrFontSize (ttFontSize sty)
                 ∷ attrFontFamily (ttFontFamily sty)
                 ∷ textAnchor_ "middle"
                 ∷ dominantBaseline_ "central"
                 ∷ [] ) ( text txt ∷ [] )
       ∷ [] )
  where
    calcBoxX : TooltipPosition → Float → Float → Float → Float
    calcBoxX Top ax tw _ = ax - tw ÷ 2.0
    calcBoxX Bottom ax tw _ = ax - tw ÷ 2.0
    calcBoxX Left ax tw arrSz = ax - tw - arrSz
    calcBoxX Right ax _ arrSz = ax + arrSz

    calcBoxY : TooltipPosition → Float → Float → Float → Float
    calcBoxY Top ay th arrSz = ay - th - arrSz
    calcBoxY Bottom ay _ arrSz = ay + arrSz
    calcBoxY Left ay th _ = ay - th ÷ 2.0
    calcBoxY Right ay th _ = ay - th ÷ 2.0

------------------------------------------------------------------------
-- Simple Tooltips
------------------------------------------------------------------------

svgTooltipSimple : ∀ {M Msg}
                 → Float → Float → String → TooltipPosition
                 → Node M Msg
svgTooltipSimple ax ay txt pos =
  svgTooltip ax ay 80.0 16.0 txt pos defaultTooltipStyle

svgTooltipTop : ∀ {M Msg}
              → Float → Float → String
              → Node M Msg
svgTooltipTop ax ay txt =
  svgTooltipSimple ax ay txt Top

svgTooltipBottom : ∀ {M Msg}
                 → Float → Float → String
                 → Node M Msg
svgTooltipBottom ax ay txt =
  svgTooltipSimple ax ay txt Bottom

svgTooltipLeft : ∀ {M Msg}
               → Float → Float → String
               → Node M Msg
svgTooltipLeft ax ay txt =
  svgTooltipSimple ax ay txt Left

svgTooltipRight : ∀ {M Msg}
                → Float → Float → String
                → Node M Msg
svgTooltipRight ax ay txt =
  svgTooltipSimple ax ay txt Right

------------------------------------------------------------------------
-- Badge / Tag
------------------------------------------------------------------------

-- Simple badge (no arrow, inline)
svgBadge : ∀ {M Msg}
         → Float → Float       -- x, y
         → String              -- text
         → String              -- bg color
         → String              -- text color
         → Node M Msg
svgBadge px py txt bg fg =
  let pad = 6.0
      estW = 40.0  -- estimated text width
      h = 20.0
  in g ( attr "class" "svg-badge" ∷ [] )
       ( rect' ( attrX px
               ∷ attrY py
               ∷ widthF (estW + pad * 2.0)
               ∷ heightF h
               ∷ fill_ bg
               ∷ rxF 10.0
               ∷ ryF 10.0
               ∷ [] ) []
       ∷ svgText ( attrX (px + estW ÷ 2.0 + pad)
                 ∷ attrY (py + h ÷ 2.0)
                 ∷ fill_ fg
                 ∷ attrFontSize "11px"
                 ∷ attrFontFamily "system-ui, sans-serif"
                 ∷ textAnchor_ "middle"
                 ∷ dominantBaseline_ "central"
                 ∷ attr "font-weight" "600"
                 ∷ [] ) ( text txt ∷ [] )
       ∷ [] )

-- Common badge variants
svgBadgeSuccess : ∀ {M Msg} → Float → Float → String → Node M Msg
svgBadgeSuccess px py txt = svgBadge px py txt "#dcfce7" "#166534"

svgBadgeWarning : ∀ {M Msg} → Float → Float → String → Node M Msg
svgBadgeWarning px py txt = svgBadge px py txt "#fef3c7" "#92400e"

svgBadgeError : ∀ {M Msg} → Float → Float → String → Node M Msg
svgBadgeError px py txt = svgBadge px py txt "#fee2e2" "#991b1b"

svgBadgeInfo : ∀ {M Msg} → Float → Float → String → Node M Msg
svgBadgeInfo px py txt = svgBadge px py txt "#dbeafe" "#1e40af"
