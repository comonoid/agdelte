{-# OPTIONS --without-K #-}

-- SvgProgress: linear and circular progress indicators
-- For showing completion, loading, or capacity

module Agdelte.Svg.Controls.Progress where

open import Data.String using (String; _++_)
open import Data.Float using (Float; _+_; _-_; _*_)
open import Data.Float.Base using (_÷_; _≤ᵇ_)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Nat using (ℕ; zero; suc; _<ᵇ_)

open import Agdelte.Reactive.Node using (Node; Attr; elem; attr; on; text)
open import Agdelte.Svg.Elements using (g; rect'; circle'; svgText)
open import Agdelte.Svg.Attributes
  hiding (x_; y_)
  renaming (xF to attrX; yF to attrY; cxF to attrCx; cyF to attrCy;
            fontSize_ to attrFontSize; fontFamily_ to attrFontFamily)
open import Agdelte.Css.Show using (showFloat)

------------------------------------------------------------------------
-- Progress Style
------------------------------------------------------------------------

record ProgressStyle : Set where
  constructor mkProgressStyle
  field
    trackColor     : String    -- background track color
    fillColor      : String    -- progress fill color
    trackSize      : Float     -- thickness (height for linear, stroke-width for circular)
    cornerRadius   : Float     -- for linear bar
    showLabel      : Bool      -- show percentage label
    labelColor     : String    -- label text color
    labelSize      : String    -- label font size

open ProgressStyle public

-- Default blue style
defaultProgressStyle : ProgressStyle
defaultProgressStyle = mkProgressStyle
  "#e5e7eb"    -- light gray track
  "#3b82f6"    -- blue fill
  8.0          -- thickness
  4.0          -- corner radius
  false        -- no label
  "#374151"    -- dark label
  "12px"

-- With label
labeledProgressStyle : ProgressStyle
labeledProgressStyle = mkProgressStyle
  "#e5e7eb"
  "#3b82f6"
  8.0
  4.0
  true         -- show label
  "#374151"
  "12px"

-- Success (green)
successProgressStyle : ProgressStyle
successProgressStyle = mkProgressStyle
  "#dcfce7"    -- light green track
  "#22c55e"    -- green fill
  8.0
  4.0
  false
  "#166534"
  "12px"

-- Warning (yellow)
warningProgressStyle : ProgressStyle
warningProgressStyle = mkProgressStyle
  "#fef3c7"    -- light yellow track
  "#f59e0b"    -- amber fill
  8.0
  4.0
  false
  "#92400e"
  "12px"

-- Error (red)
errorProgressStyle : ProgressStyle
errorProgressStyle = mkProgressStyle
  "#fee2e2"    -- light red track
  "#ef4444"    -- red fill
  8.0
  4.0
  false
  "#991b1b"
  "12px"

------------------------------------------------------------------------
-- Helpers
------------------------------------------------------------------------

private
  clamp01 : Float → Float
  clamp01 v = if v ≤ᵇ 0.0 then 0.0 else if 1.0 ≤ᵇ v then 1.0 else v

  -- Format percentage (0-100)
  formatPercent : Float → String
  formatPercent ratio =
    let pct = ratio * 100.0
    in showFloat pct ++ "%"

  -- π constant
  π : Float
  π = 3.14159265359

------------------------------------------------------------------------
-- Linear Progress Bar
------------------------------------------------------------------------

svgProgressBar : ∀ {M Msg}
               → Float → Float → Float   -- x, y, width
               → Float                   -- value (0-1)
               → ProgressStyle
               → Node M Msg
svgProgressBar px py w val sty =
  let ratio = clamp01 val
      h = trackSize sty
      fillW = ratio * w
  in g ( attr "class" "svg-progress-bar" ∷ [] )
       ( -- Track
         rect' ( attrX px
               ∷ attrY py
               ∷ widthF w
               ∷ heightF h
               ∷ fill_ (trackColor sty)
               ∷ rxF (cornerRadius sty)
               ∷ ryF (cornerRadius sty)
               ∷ [] ) []
       -- Fill
       ∷ rect' ( attrX px
               ∷ attrY py
               ∷ widthF fillW
               ∷ heightF h
               ∷ fill_ (fillColor sty)
               ∷ rxF (cornerRadius sty)
               ∷ ryF (cornerRadius sty)
               ∷ [] ) []
       -- Label (optional)
       ∷ (if showLabel sty
          then svgText ( attrX (px + w + 8.0)
                       ∷ attrY (py + h ÷ 2.0)
                       ∷ fill_ (labelColor sty)
                       ∷ attrFontSize (labelSize sty)
                       ∷ attrFontFamily "system-ui, sans-serif"
                       ∷ dominantBaseline_ "central"
                       ∷ [] ) ( text (formatPercent ratio) ∷ [] )
          else g [] [])
       ∷ [] )

------------------------------------------------------------------------
-- Linear Progress with Label Inside
------------------------------------------------------------------------

svgProgressBarInline : ∀ {M Msg}
                     → Float → Float → Float  -- x, y, width
                     → Float                  -- value (0-1)
                     → ProgressStyle
                     → Node M Msg
svgProgressBarInline px py w val sty =
  let ratio = clamp01 val
      h = trackSize sty + 8.0  -- taller to fit text
      fillW = ratio * w
  in g ( attr "class" "svg-progress-bar-inline" ∷ [] )
       ( -- Track
         rect' ( attrX px
               ∷ attrY py
               ∷ widthF w
               ∷ heightF h
               ∷ fill_ (trackColor sty)
               ∷ rxF (cornerRadius sty)
               ∷ ryF (cornerRadius sty)
               ∷ [] ) []
       -- Fill
       ∷ rect' ( attrX px
               ∷ attrY py
               ∷ widthF fillW
               ∷ heightF h
               ∷ fill_ (fillColor sty)
               ∷ rxF (cornerRadius sty)
               ∷ ryF (cornerRadius sty)
               ∷ [] ) []
       -- Label centered
       ∷ svgText ( attrX (px + w ÷ 2.0)
                 ∷ attrY (py + h ÷ 2.0)
                 ∷ fill_ "#ffffff"
                 ∷ attrFontSize (labelSize sty)
                 ∷ attrFontFamily "system-ui, sans-serif"
                 ∷ textAnchor_ "middle"
                 ∷ dominantBaseline_ "central"
                 ∷ attr "font-weight" "600"
                 ∷ [] ) ( text (formatPercent ratio) ∷ [] )
       ∷ [] )

------------------------------------------------------------------------
-- Circular Progress
------------------------------------------------------------------------

svgProgressCircle : ∀ {M Msg}
                  → Float → Float       -- cx, cy (center)
                  → Float               -- radius
                  → Float               -- value (0-1)
                  → ProgressStyle
                  → Node M Msg
svgProgressCircle cx cy radius val sty =
  let ratio = clamp01 val
      -- Circle arc via stroke-dasharray/dashoffset
      circumference = 2.0 * π * radius
      dashoffset = circumference * (1.0 - ratio)
      sw = trackSize sty
  in g ( attr "class" "svg-progress-circle" ∷ [] )
       ( -- Track circle
         circle' ( attrCx cx
                 ∷ attrCy cy
                 ∷ rF radius
                 ∷ fill_ "none"
                 ∷ stroke_ (trackColor sty)
                 ∷ strokeWidthF sw
                 ∷ [] ) []
       -- Progress arc
       ∷ circle' ( attrCx cx
                 ∷ attrCy cy
                 ∷ rF radius
                 ∷ fill_ "none"
                 ∷ stroke_ (fillColor sty)
                 ∷ strokeWidthF sw
                 ∷ attr "stroke-linecap" "round"
                 ∷ attr "stroke-dasharray" (showFloat circumference)
                 ∷ attr "stroke-dashoffset" (showFloat dashoffset)
                 -- Rotate -90deg to start from top
                 ∷ attr "transform" ("rotate(-90 " ++ showFloat cx ++ " " ++ showFloat cy ++ ")")
                 ∷ [] ) []
       -- Label (optional)
       ∷ (if showLabel sty
          then svgText ( attrX cx
                       ∷ attrY cy
                       ∷ fill_ (labelColor sty)
                       ∷ attrFontSize (labelSize sty)
                       ∷ attrFontFamily "system-ui, sans-serif"
                       ∷ textAnchor_ "middle"
                       ∷ dominantBaseline_ "central"
                       ∷ attr "font-weight" "600"
                       ∷ [] ) ( text (formatPercent ratio) ∷ [] )
          else g [] [])
       ∷ [] )

------------------------------------------------------------------------
-- Simple Progress Bars (default style)
------------------------------------------------------------------------

svgProgressSimple : ∀ {M Msg}
                  → Float → Float → Float → Float
                  → Node M Msg
svgProgressSimple px py w val =
  svgProgressBar px py w val defaultProgressStyle

svgProgressSimpleLabeled : ∀ {M Msg}
                         → Float → Float → Float → Float
                         → Node M Msg
svgProgressSimpleLabeled px py w val =
  svgProgressBar px py w val labeledProgressStyle

------------------------------------------------------------------------
-- Simple Circular Progress
------------------------------------------------------------------------

svgProgressCircleSimple : ∀ {M Msg}
                        → Float → Float → Float → Float
                        → Node M Msg
svgProgressCircleSimple cx cy r val =
  svgProgressCircle cx cy r val defaultProgressStyle

svgProgressCircleLabeled : ∀ {M Msg}
                         → Float → Float → Float → Float
                         → Node M Msg
svgProgressCircleLabeled cx cy r val =
  svgProgressCircle cx cy r val labeledProgressStyle

------------------------------------------------------------------------
-- Indeterminate Spinner
------------------------------------------------------------------------

-- Simple spinning circle (uses CSS animation class)
svgSpinner : ∀ {M Msg}
           → Float → Float → Float  -- cx, cy, radius
           → String                 -- color
           → Node M Msg
svgSpinner cx cy r color =
  g ( attr "class" "svg-spinner" ∷ [] )
    ( circle' ( attrCx cx
              ∷ attrCy cy
              ∷ rF r
              ∷ fill_ "none"
              ∷ stroke_ color
              ∷ strokeWidthF 3.0
              ∷ attr "stroke-linecap" "round"
              ∷ attr "stroke-dasharray" (showFloat (2.0 * π * r * 0.25) ++ " " ++ showFloat (2.0 * π * r * 0.75))
              ∷ [] ) []
    ∷ [] )

------------------------------------------------------------------------
-- Multi-segment Progress (for multi-step wizards)
------------------------------------------------------------------------

svgProgressSegments : ∀ {M Msg}
                    → Float → Float → Float  -- x, y, width
                    → Float                  -- height
                    → ℕ                      -- completed (0-N)
                    → ℕ                      -- total segments
                    → ProgressStyle
                    → Node M Msg
svgProgressSegments {M} {Msg} px py w h completed total sty =
  let totalF = Data.Float.Base.fromℕ total
      gap = 4.0
      segW = (w - gap * (totalF - 1.0)) ÷ totalF
  in g ( attr "class" "svg-progress-segments" ∷ [] )
       (renderSegs total 0 px)
  where
    totalF' = Data.Float.Base.fromℕ total
    gap' = 4.0
    segW' = (w - gap' * (totalF' - 1.0)) ÷ totalF'

    renderSegs : ℕ → ℕ → Float → List (Node M Msg)
    renderSegs zero _ _ = []
    renderSegs (suc remaining) idx currentX =
      let isFilled = idx <ᵇ completed
          c = if isFilled then fillColor sty else trackColor sty
      in rect' ( attrX currentX
               ∷ attrY py
               ∷ widthF segW'
               ∷ heightF h
               ∷ fill_ c
               ∷ rxF 2.0
               ∷ ryF 2.0
               ∷ [] ) []
         ∷ renderSegs remaining (suc idx) (currentX + segW' + gap')
