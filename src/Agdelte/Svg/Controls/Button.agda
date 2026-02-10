{-# OPTIONS --without-K #-}

-- SvgButton: SVG button with hover/active states
-- Pure SVG button for dashboards, visualizations, games

module Agdelte.Svg.Controls.Button where

open import Data.String using (String; _++_)
open import Data.Float using (Float; _+_; _-_; _*_)
open import Data.Float.Base using (_÷_)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)

open import Agdelte.Reactive.Node using (Node; Attr; elem; attr; on; text)
open import Agdelte.Svg.Elements using (g; rect'; svgText)
open import Agdelte.Svg.Attributes
  hiding (x_; y_)
  renaming (xF to attrX; yF to attrY; fontSize_ to attrFontSize; fontFamily_ to attrFontFamily)
open import Agdelte.Css.Show using (showFloat)

------------------------------------------------------------------------
-- Button Style
------------------------------------------------------------------------

record SvgButtonStyle : Set where
  constructor mkStyle
  field
    bgColor       : String    -- background color
    bgHover       : String    -- background on hover
    bgActive      : String    -- background on press
    textColor     : String    -- text color
    borderColor   : String    -- border stroke
    borderWidth   : Float     -- border stroke width
    cornerRadius  : Float     -- rx/ry for rounded corners
    fntSize       : String    -- font size (e.g. "14px")
    fntFamily     : String    -- font family

open SvgButtonStyle public

-- Default style (dark theme)
defaultStyle : SvgButtonStyle
defaultStyle = mkStyle
  "#3b82f6"    -- blue bg
  "#2563eb"    -- darker blue on hover
  "#1d4ed8"    -- even darker on active
  "#ffffff"    -- white text
  "#1e40af"    -- border
  1.5          -- border width
  6.0          -- corner radius
  "14px"       -- font size
  "system-ui, sans-serif"

-- Light theme style
lightStyle : SvgButtonStyle
lightStyle = mkStyle
  "#e5e7eb"    -- gray bg
  "#d1d5db"    -- darker gray on hover
  "#9ca3af"    -- even darker on active
  "#1f2937"    -- dark text
  "#9ca3af"    -- border
  1.0          -- border width
  4.0          -- corner radius
  "14px"       -- font size
  "system-ui, sans-serif"

-- Ghost style (transparent bg)
ghostStyle : SvgButtonStyle
ghostStyle = mkStyle
  "transparent" -- no bg
  "#f3f4f6"     -- light gray on hover
  "#e5e7eb"     -- gray on active
  "#374151"     -- dark text
  "transparent" -- no border
  0.0           -- no border
  4.0           -- corner radius
  "14px"        -- font size
  "system-ui, sans-serif"

------------------------------------------------------------------------
-- Button State (for tracking hover/active)
------------------------------------------------------------------------

data ButtonState : Set where
  Idle    : ButtonState
  Hovered : ButtonState
  Active  : ButtonState

------------------------------------------------------------------------
-- Button Config
------------------------------------------------------------------------

record SvgButtonConfig (M Msg : Set) : Set where
  constructor mkConfig
  field
    posX      : Float           -- x position
    posY      : Float           -- y position
    btnWidth  : Float           -- button width
    btnHeight : Float           -- button height
    btnLabel  : String          -- button text
    btnStyle  : SvgButtonStyle  -- visual style
    getState  : M → ButtonState -- extract button state from model
    onClick   : Msg             -- message on click
    onHover   : Msg             -- message on mouseenter
    onLeave   : Msg             -- message on mouseleave
    onDown    : Msg             -- message on mousedown
    onUp      : Msg             -- message on mouseup

open SvgButtonConfig public

------------------------------------------------------------------------
-- Simple Button (no hover/active tracking in model)
------------------------------------------------------------------------

-- Simple button that just fires onClick, no state tracking
svgButton : ∀ {M Msg}
          → Float → Float → Float → Float  -- x, y, width, height
          → String                          -- label
          → SvgButtonStyle                  -- style
          → Msg                             -- onClick
          → Node M Msg
svgButton px py w h lbl sty msg =
  g ( attr "class" "svg-button"
    ∷ attr "cursor" "pointer"
    ∷ [] )
    ( rect' ( attrX px
            ∷ attrY py
            ∷ widthF w
            ∷ heightF h
            ∷ fill_ (bgColor sty)
            ∷ stroke_ (borderColor sty)
            ∷ strokeWidthF (borderWidth sty)
            ∷ rxF (cornerRadius sty)
            ∷ ryF (cornerRadius sty)
            ∷ on "click" msg
            ∷ [] ) []
    ∷ svgText ( attrX (px + w ÷ 2.0)
              ∷ attrY (py + h ÷ 2.0)
              ∷ fill_ (textColor sty)
              ∷ attrFontSize (fntSize sty)
              ∷ attrFontFamily (fntFamily sty)
              ∷ textAnchor_ "middle"
              ∷ dominantBaseline_ "central"
              ∷ attr "pointer-events" "none"
              ∷ [] ) ( text lbl ∷ [] )
    ∷ [] )

-- Simple button with default style
svgButtonDefault : ∀ {M Msg}
                 → Float → Float → Float → Float
                 → String → Msg
                 → Node M Msg
svgButtonDefault px py w h lbl msg =
  svgButton px py w h lbl defaultStyle msg

------------------------------------------------------------------------
-- Stateful Button (with hover/active tracking)
------------------------------------------------------------------------

-- Button that changes appearance based on state
svgButtonStateful : ∀ {M Msg}
                  → SvgButtonConfig M Msg
                  → Node M Msg
svgButtonStateful cfg =
  let s = btnStyle cfg
  in g ( attr "class" "svg-button-stateful"
       ∷ attr "cursor" "pointer"
       ∷ [] )
       ( rect' ( attrX (posX cfg)
               ∷ attrY (posY cfg)
               ∷ widthF (btnWidth cfg)
               ∷ heightF (btnHeight cfg)
               ∷ attr "fill" (bgColor s)
               ∷ stroke_ (borderColor s)
               ∷ strokeWidthF (borderWidth s)
               ∷ rxF (cornerRadius s)
               ∷ ryF (cornerRadius s)
               ∷ on "click" (onClick cfg)
               ∷ on "mouseenter" (onHover cfg)
               ∷ on "mouseleave" (onLeave cfg)
               ∷ on "mousedown" (onDown cfg)
               ∷ on "mouseup" (onUp cfg)
               ∷ [] ) []
       ∷ svgText ( attrX (posX cfg + btnWidth cfg ÷ 2.0)
                 ∷ attrY (posY cfg + btnHeight cfg ÷ 2.0)
                 ∷ fill_ (textColor s)
                 ∷ attrFontSize (fntSize s)
                 ∷ attrFontFamily (fntFamily s)
                 ∷ textAnchor_ "middle"
                 ∷ dominantBaseline_ "central"
                 ∷ attr "pointer-events" "none"
                 ∷ [] ) ( text (btnLabel cfg) ∷ [] )
       ∷ [] )

------------------------------------------------------------------------
-- Icon Button
------------------------------------------------------------------------

-- Button with just an icon (path d string)
svgIconButton : ∀ {M Msg}
              → Float → Float → Float  -- x, y, size
              → String                  -- SVG path d
              → SvgButtonStyle
              → Msg
              → Node M Msg
svgIconButton px py size pathD sty msg =
  let padding = size * 0.2
      iconSize = size - padding * 2.0
  in g ( attr "class" "svg-icon-button"
       ∷ attr "cursor" "pointer"
       ∷ [] )
       ( rect' ( attrX px
               ∷ attrY py
               ∷ widthF size
               ∷ heightF size
               ∷ fill_ (bgColor sty)
               ∷ stroke_ (borderColor sty)
               ∷ strokeWidthF (borderWidth sty)
               ∷ rxF (cornerRadius sty)
               ∷ ryF (cornerRadius sty)
               ∷ on "click" msg
               ∷ [] ) []
       ∷ elem "path" ( d_ pathD
                     ∷ fill_ (textColor sty)
                     ∷ transform_ ("translate(" ++ showFloat (px + padding) ++ ","
                                ++ showFloat (py + padding) ++ ") scale("
                                ++ showFloat (iconSize ÷ 24.0) ++ ")")
                     ∷ attr "pointer-events" "none"
                     ∷ [] ) []
       ∷ [] )

------------------------------------------------------------------------
-- Common Icon Paths (24x24 viewBox)
------------------------------------------------------------------------

-- Plus icon
iconPlus : String
iconPlus = "M12 4v16m-8-8h16"

-- Minus icon
iconMinus : String
iconMinus = "M4 12h16"

-- Close/X icon
iconClose : String
iconClose = "M6 6l12 12m0-12L6 18"

-- Check icon
iconCheck : String
iconCheck = "M5 12l5 5L19 7"

-- Arrow left
iconArrowLeft : String
iconArrowLeft = "M15 18l-6-6 6-6"

-- Arrow right
iconArrowRight : String
iconArrowRight = "M9 6l6 6-6 6"

-- Arrow up
iconArrowUp : String
iconArrowUp = "M18 15l-6-6-6 6"

-- Arrow down
iconArrowDown : String
iconArrowDown = "M6 9l6 6 6-6"

------------------------------------------------------------------------
-- Button Group
------------------------------------------------------------------------

-- Horizontal group of buttons
svgButtonGroup : ∀ {M Msg}
               → Float → Float           -- x, y
               → Float → Float           -- button width, height
               → Float                   -- gap between buttons
               → SvgButtonStyle
               → List (String × Msg)     -- label-message pairs
               → Node M Msg
svgButtonGroup {M} {Msg} px py w h gap sty [] = g [] []
svgButtonGroup {M} {Msg} px py w h gap sty ((lbl , msg) ∷ rest) =
  g []
    ( svgButton px py w h lbl sty msg
    ∷ renderRest (px + w + gap) rest
    )
  where
    renderRest : Float → List (String × Msg) → List (Node M Msg)
    renderRest _ [] = []
    renderRest px' ((l , m) ∷ rs) =
      svgButton px' py w h l sty m ∷ renderRest (px' + w + gap) rs
