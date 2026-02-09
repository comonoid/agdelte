{-# OPTIONS --without-K #-}

-- SVG Line Drawing Animation Demo
-- Uses stroke-dasharray/dashoffset for "self-drawing" effect
-- Click "Draw" to animate - uses SMIL for smooth animation

module SvgLineDraw where

open import Data.List using (List; []; _∷_; [_])
open import Data.Nat using (ℕ; zero; suc)
open import Data.Float using (Float; _+_; _-_; _*_)
open import Data.String using (String; _++_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Unit using (⊤; tt)

open import Agdelte.Reactive.Node
open import Agdelte.Css.Color using (hex)
open import Agdelte.Css.Show using (showFloat)
open import Agdelte.Svg

------------------------------------------------------------------------
-- Model
------------------------------------------------------------------------

record Model : Set where
  constructor mkModel
  field
    animKey : ℕ   -- increment to restart animation

initModel : Model
initModel = mkModel 0

------------------------------------------------------------------------
-- Messages
------------------------------------------------------------------------

data Msg : Set where
  StartDraw : Msg
  Reset     : Msg

------------------------------------------------------------------------
-- Update
------------------------------------------------------------------------

updateModel : Msg → Model → Model
updateModel StartDraw m = record m { animKey = suc (Model.animKey m) }
updateModel Reset m = mkModel 0

------------------------------------------------------------------------
-- Paths
------------------------------------------------------------------------

-- Star path (5 points)
starPath : String
starPath = "M150 20 L179 90 L255 90 L194 140 L218 215 L150 170 L82 215 L106 140 L45 90 L121 90 Z"

starLength : Float
starLength = 530.0

-- Signature-like path
signaturePath : String
signaturePath = "M30 150 Q80 50 130 150 T230 150 Q280 100 330 150 T430 100"

signatureLength : Float
signatureLength = 450.0

-- Heart path
heartPath : String
heartPath = "M75 40 C50 0 0 25 0 65 C0 100 75 140 75 140 C75 140 150 100 150 65 C150 25 100 0 75 40"

heartLength : Float
heartLength = 350.0

------------------------------------------------------------------------
-- View
------------------------------------------------------------------------

-- Drawing path with SMIL animation for line drawing
-- Shows dotted outline initially, draws solid on click
drawingPathSmil : String → Float → String → Float → String → Node Model Msg
drawingPathSmil pathD len strokeColor strokeW animId =
  g (attr "cursor" "pointer" ∷ [])
    ( -- Invisible clickable area (wider stroke for easier clicking)
      path' ( d_ pathD
            ∷ stroke_ "transparent"
            ∷ strokeWidthF 20.0
            ∷ fill_ "none"
            ∷ [])
        ( -- This dummy animate has the ID, triggered by click on this path
          animate "opacity" "1" "1"
            (withId animId (onClick' (record defaultSmil { dur = sec 2.0 })))
        ∷ [] )
    ∷ -- Background: dotted outline (always visible)
      path' ( d_ pathD
            ∷ stroke_ "#ccc"
            ∷ strokeWidthF (strokeW + 1.0)
            ∷ fill_ "none"
            ∷ strokeLinecap_ "round"
            ∷ strokeLinejoin_ "round"
            ∷ attr "stroke-dasharray" "6 6"
            ∷ attr "pointer-events" "none"
            ∷ [])
        []
    ∷ -- Foreground: the "drawing" path (hidden initially)
      path' ( d_ pathD
            ∷ stroke_ strokeColor
            ∷ strokeWidthF strokeW
            ∷ fill_ "none"
            ∷ strokeLinecap_ "round"
            ∷ strokeLinejoin_ "round"
            ∷ attr "stroke-dasharray" (showFloat len)
            ∷ attr "stroke-dashoffset" (showFloat len)
            ∷ attr "pointer-events" "none"
            ∷ [])
        ( -- Animate stroke-dashoffset from len to 0
          animate "stroke-dashoffset" (showFloat len) "0"
            (freezeEnd (record defaultSmil
              { dur = sec 2.0
              ; begin' = syncBegin animId
              }))
        ∷ [] )
    ∷ [] )

-- Demo: Star (left side)
starDemo : Node Model Msg
starDemo =
  g (transform_ "translate(20, 20)" ∷ [])
    ( svgText (x_ "130" ∷ y_ "0" ∷ textAnchor_ "middle" ∷ fontSize_ "14" ∷ fill_ "#666" ∷ [])
        [ text "Star (click)" ]
    ∷ drawingPathSmil starPath starLength "#4a9eff" 3.0 "starAnim"
    ∷ [] )

-- Demo: Heart (right side)
heartDemo : Node Model Msg
heartDemo =
  g (transform_ "translate(340, 50)" ∷ [])
    ( svgText (x_ "75" ∷ y_ "0" ∷ textAnchor_ "middle" ∷ fontSize_ "14" ∷ fill_ "#666" ∷ [])
        [ text "Heart (click)" ]
    ∷ drawingPathSmil heartPath heartLength "#ec4899" 4.0 "heartAnim"
    ∷ [] )

-- Demo: Signature (bottom, scaled down)
signatureDemo : Node Model Msg
signatureDemo =
  g (transform_ "translate(50, 300)" ∷ [])
    ( svgText (x_ "220" ∷ y_ "-20" ∷ textAnchor_ "middle" ∷ fontSize_ "14" ∷ fill_ "#666" ∷ [])
        [ text "Signature (click)" ]
    ∷ g (transform_ "scale(1, 0.8) translate(0, -50)" ∷ [])
        [ drawingPathSmil signaturePath signatureLength "#10b981" 4.0 "sigAnim" ]
    ∷ [] )

-- Instructions
instructions : Node Model Msg
instructions =
  div (style "margin-top" "15px" ∷ style "color" "#666" ∷ [])
    [ text "Click each shape to see it draw itself using SMIL animation" ]

-- Main template
lineDrawTemplate : Node Model Msg
lineDrawTemplate =
  div [ class "line-draw-demo" ]
    ( h1 [] [ text "SVG Line Drawing Animation" ]
    ∷ p (style "color" "#666" ∷ [])
        [ text "Uses stroke-dasharray trick with SMIL animate" ]
    ∷ svg ( viewBox_ "0 0 550 450"
          ∷ width_ "550" ∷ height_ "450"
          ∷ style "background" "#fafafa"
          ∷ style "border-radius" "8px"
          ∷ [])
        ( rect' (width_ "550" ∷ height_ "450" ∷ fill_ "#fafafa" ∷ []) []
        ∷ starDemo
        ∷ signatureDemo
        ∷ heartDemo
        ∷ [] )
    ∷ instructions
    ∷ [] )

------------------------------------------------------------------------
-- App
------------------------------------------------------------------------

lineDrawApp : ReactiveApp Model Msg
lineDrawApp = simpleApp initModel updateModel lineDrawTemplate

app : ReactiveApp Model Msg
app = lineDrawApp
