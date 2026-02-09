{-# OPTIONS --without-K #-}

-- Interactive SVG Pan/Zoom Demo
-- Demonstrates SVG events with coordinate conversion

module SvgPanZoom where

open import Data.List using (List; []; _∷_; [_]; map) renaming (_++_ to _++L_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show using (show)
open import Data.Float using (Float; _+_; _-_; _*_; _÷_; _<ᵇ_)
open import Data.String using (String; _++_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Unit using (⊤; tt)

open import Agdelte.Reactive.Node
open import Agdelte.Css.Color using (hex; rgba; named)
open import Agdelte.Css.Show using (showFloat)
open import Agdelte.Svg

------------------------------------------------------------------------
-- Model
------------------------------------------------------------------------

record Model : Set where
  constructor mkModel
  field
    viewBox   : ViewBox
    isDragging : Bool
    lastX     : Float
    lastY     : Float

initModel : Model
initModel = mkModel
  (mkViewBox 0.0 0.0 400.0 300.0)
  false
  0.0
  0.0

------------------------------------------------------------------------
-- Messages
------------------------------------------------------------------------

data Msg : Set where
  StartDrag : Point → Msg
  Drag      : Point → Msg
  StopDrag  : Msg
  ZoomIn    : Msg
  ZoomOut   : Msg
  Reset     : Msg
  Wheel     : Float → Msg

------------------------------------------------------------------------
-- Update
------------------------------------------------------------------------

updateModel : Msg → Model → Model
updateModel (StartDrag p) m = record m
  { isDragging = true
  ; lastX = Point.x p
  ; lastY = Point.y p
  }
updateModel (Drag p) m with Model.isDragging m
... | false = m
... | true =
  let screenDx = Point.x p - Model.lastX m
      screenDy = Point.y p - Model.lastY m
      vb = Model.viewBox m
      -- Scale screen pixels to viewBox units
      -- SVG is 600x450 screen pixels, viewBox is variable
      scaledDx = screenDx * (ViewBox.width vb ÷ 600.0)
      scaledDy = screenDy * (ViewBox.height vb ÷ 450.0)
      -- Pan in opposite direction (drag moves content)
      newVB = panViewBox (0.0 - scaledDx) (0.0 - scaledDy) vb
  in record m
    { viewBox = newVB
    ; lastX = Point.x p
    ; lastY = Point.y p
    }
updateModel StopDrag m = record m { isDragging = false }
updateModel ZoomIn m = record m
  { viewBox = zoomViewBox 1.2 (Model.viewBox m) }
updateModel ZoomOut m = record m
  { viewBox = zoomViewBox 0.8 (Model.viewBox m) }
updateModel Reset m = record m
  { viewBox = mkViewBox 0.0 0.0 400.0 300.0 }
updateModel (Wheel delta) m =
  let factor = if 0.0 <ᵇ delta then 1.1 else 0.9
  in record m { viewBox = zoomViewBox factor (Model.viewBox m) }

------------------------------------------------------------------------
-- View: Grid with shapes
------------------------------------------------------------------------

-- Helper
toFloat : ℕ → Float
toFloat zero = 0.0
toFloat (suc n) = 1.0 + toFloat n

-- Generate grid lines
gridLines : List (Node Model Msg)
gridLines =
  map (λ i →
    line' ( x1F (toFloat i * 50.0) ∷ y1F 0.0
          ∷ x2F (toFloat i * 50.0) ∷ y2F 300.0
          ∷ stroke_ "#e5e7eb" ∷ strokeWidth_ "1" ∷ []) [])
    (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ [])

gridLinesH : List (Node Model Msg)
gridLinesH =
  map (λ i →
    line' ( x1F 0.0 ∷ y1F (toFloat i * 50.0)
          ∷ x2F 400.0 ∷ y2F (toFloat i * 50.0)
          ∷ stroke_ "#e5e7eb" ∷ strokeWidth_ "1" ∷ []) [])
    (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ [])

-- Sample shapes
shapes : List (Node Model Msg)
shapes =
  -- Blue circle
  circle' (cxF 100.0 ∷ cyF 100.0 ∷ rF 40.0 ∷ fillC (hex "#4a9eff") ∷ []) []
  ∷ -- Green rectangle
  rect' (xF 200.0 ∷ yF 60.0 ∷ widthF 80.0 ∷ heightF 80.0 ∷ fillC (hex "#10b981") ∷ rx_ "8" ∷ []) []
  ∷ -- Purple triangle
  polygon' (points_ "300,200 340,280 260,280" ∷ fillC (hex "#8b5cf6") ∷ []) []
  ∷ -- Orange ellipse
  ellipse' (cxF 100.0 ∷ cyF 230.0 ∷ rxF 50.0 ∷ ryF 30.0 ∷ fillC (hex "#f59e0b") ∷ []) []
  ∷ -- Coordinate labels
  svgText (xF 50.0 ∷ yF 20.0 ∷ fontSize_ "12" ∷ fill_ "#999" ∷ [])
    [ text "(50, 20)" ]
  ∷ svgText (xF 350.0 ∷ yF 280.0 ∷ fontSize_ "12" ∷ fill_ "#999" ∷ [])
    [ text "(350, 280)" ]
  ∷ []

-- Control buttons
controls : Node Model Msg
controls =
  div (style "margin-top" "10px" ∷ style "display" "flex" ∷ style "justify-content" "center" ∷ style "gap" "8px" ∷ [])
    ( button (onClick ZoomIn ∷ style "padding" "8px 16px" ∷ []) [ text "Zoom In (+)" ]
    ∷ button (onClick ZoomOut ∷ style "padding" "8px 16px" ∷ []) [ text "Zoom Out (-)" ]
    ∷ button (onClick Reset ∷ style "padding" "8px 16px" ∷ []) [ text "Reset" ]
    ∷ [] )

-- ViewBox info display
viewBoxInfo : Node Model Msg
viewBoxInfo =
  div (style "margin-top" "10px" ∷ style "font-family" "monospace" ∷ style "color" "#666" ∷ [])
    ( bind (stringBinding λ m →
        let vb = Model.viewBox m
        in "ViewBox: " ++
           showFloat (ViewBox.minX vb) ++ " " ++
           showFloat (ViewBox.minY vb) ++ " " ++
           showFloat (ViewBox.width vb) ++ " " ++
           showFloat (ViewBox.height vb))
    ∷ [] )

-- Main template
panZoomTemplate : Node Model Msg
panZoomTemplate =
  div (class "pan-zoom-demo" ∷ style "text-align" "center" ∷ [])
    ( h1 [] [ text "Interactive SVG Pan/Zoom" ]
    ∷ p (style "color" "#666" ∷ [])
        [ text "Drag to pan, use buttons to zoom. Coordinates in SVG space." ]
    ∷ svg ( attrBind "viewBox" (stringBinding λ m → showViewBox (Model.viewBox m))
          ∷ width_ "600" ∷ height_ "450"
          ∷ style "border" "1px solid #ddd"
          ∷ style "border-radius" "8px"
          ∷ style "cursor" "grab"
          ∷ style "background" "#fafafa"
          ∷ onScreenPointerDown StartDrag
          ∷ onScreenPointerMove Drag
          ∷ onScreenPointerUp (λ _ → StopDrag)
          ∷ onSvgPointerLeave StopDrag
          ∷ onSvgWheel Wheel
          ∷ [])
        ( -- Background
          rect' (xF 0.0 ∷ yF 0.0 ∷ widthF 400.0 ∷ heightF 300.0 ∷ fill_ "white" ∷ []) []
        ∷ gridLines
        ++L gridLinesH
        ++L shapes )
    ∷ controls
    ∷ viewBoxInfo
    ∷ [] )

------------------------------------------------------------------------
-- App
------------------------------------------------------------------------

panZoomApp : ReactiveApp Model Msg
panZoomApp = simpleApp initModel updateModel panZoomTemplate

app : ReactiveApp Model Msg
app = panZoomApp
