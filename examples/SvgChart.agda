{-# OPTIONS --without-K #-}

-- SVG Data Visualization Demo
-- Interactive bar chart with foreach and reactive bindings

module SvgChart where

open import Data.List using (List; []; _∷_; [_]; map; length)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _<ᵇ_; _≡ᵇ_)
open import Data.Nat.Show using (show)
open import Data.Float as Float using (Float) renaming (_+_ to _+F_; _-_ to _-F_; _*_ to _*F_; _÷_ to _÷F_)
open import Data.String using (String; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Unit using (⊤; tt)

open import Agdelte.Reactive.Node hiding (label; value)
open import Agdelte.Css.Color using (hex; Color; showColor)
open import Agdelte.Css.Show using (showFloat)
open import Agdelte.Svg

------------------------------------------------------------------------
-- Data types
------------------------------------------------------------------------

record BarData : Set where
  constructor mkBar
  field
    barLabel : String
    barValue : ℕ
    barColor : Color

------------------------------------------------------------------------
-- Model
------------------------------------------------------------------------

record Model : Set where
  constructor mkModel
  field
    bars : List BarData
    selectedIdx : ℕ
    hoveredIdx : ℕ  -- 999 means none

initBars : List BarData
initBars =
    mkBar "Jan" 65 (hex "#4a9eff")
  ∷ mkBar "Feb" 45 (hex "#10b981")
  ∷ mkBar "Mar" 80 (hex "#8b5cf6")
  ∷ mkBar "Apr" 55 (hex "#f59e0b")
  ∷ mkBar "May" 90 (hex "#ec4899")
  ∷ mkBar "Jun" 70 (hex "#06b6d4")
  ∷ []

initModel : Model
initModel = mkModel initBars 999 999  -- 999 means no selection

------------------------------------------------------------------------
-- Messages
------------------------------------------------------------------------

data Msg : Set where
  SelectBar : ℕ → Msg
  Deselect  : Msg
  HoverBar  : ℕ → Msg
  LeaveBar  : Msg
  AddValue  : ℕ → Msg
  SubValue  : ℕ → Msg
  AddSelected : Msg      -- Add to selected bar
  SubSelected : Msg      -- Subtract from selected bar
  WheelSelected : Float → Msg  -- Wheel on selected bar

------------------------------------------------------------------------
-- Update
------------------------------------------------------------------------

-- Update bar at index
updateBarAt : ℕ → (BarData → BarData) → List BarData → List BarData
updateBarAt _ _ [] = []
updateBarAt zero f (b ∷ bs) = f b ∷ bs
updateBarAt (suc n) f (b ∷ bs) = b ∷ updateBarAt n f bs

-- Clamp value
clamp : ℕ → ℕ → ℕ → ℕ
clamp min max n with n <ᵇ min
... | true = min
... | false with max <ᵇ n
...   | true = max
...   | false = n

addToBar : ℕ → BarData → BarData
addToBar n b = record b { barValue = clamp 0 100 (BarData.barValue b + n) }

subFromBar : ℕ → BarData → BarData
subFromBar n b = record b { barValue = clamp 0 100 (BarData.barValue b ∸ n) }

updateModel : Msg → Model → Model
updateModel (SelectBar idx) m = record m { selectedIdx = idx }
updateModel Deselect m = record m { selectedIdx = 999 }
updateModel (HoverBar idx) m = record m { hoveredIdx = idx }
updateModel LeaveBar m = record m { hoveredIdx = 999 }
updateModel (AddValue idx) m = record m
  { bars = updateBarAt idx (addToBar 10) (Model.bars m) }
updateModel (SubValue idx) m = record m
  { bars = updateBarAt idx (subFromBar 10) (Model.bars m) }
updateModel AddSelected m =
  if Model.selectedIdx m <ᵇ 900
  then record m { bars = updateBarAt (Model.selectedIdx m) (addToBar 10) (Model.bars m) }
  else m
updateModel SubSelected m =
  if Model.selectedIdx m <ᵇ 900
  then record m { bars = updateBarAt (Model.selectedIdx m) (subFromBar 10) (Model.bars m) }
  else m
updateModel (WheelSelected delta) m =
  let -- Use hovered bar if hovering, otherwise selected bar
      idx = if Model.hoveredIdx m <ᵇ 900 then Model.hoveredIdx m else Model.selectedIdx m
      f = if primFloatLess 0.0 delta then subFromBar 5 else addToBar 5
  in if idx <ᵇ 900  -- Only update if there's a valid target
     then record m { bars = updateBarAt idx f (Model.bars m) }
     else m
  where
    open import Agda.Builtin.Float using (primFloatLess)

------------------------------------------------------------------------
-- View
------------------------------------------------------------------------

-- Chart dimensions
chartWidth : Float
chartWidth = 500.0

chartHeight : Float
chartHeight = 300.0

barWidth : Float
barWidth = 60.0

barGap : Float
barGap = 20.0

maxValue : Float
maxValue = 100.0

-- Convert natural to float
toFloat : ℕ → Float
toFloat zero = 0.0
toFloat (suc n) = 1.0 +F toFloat n

-- Index bars
indexBars : List BarData → List (BarData × ℕ)
indexBars = go 0
  where
    go : ℕ → List BarData → List (BarData × ℕ)
    go _ [] = []
    go n (b ∷ bs) = (b , n) ∷ go (suc n) bs

-- Get value at index
getValueAt : ℕ → List BarData → ℕ
getValueAt _ [] = 0
getValueAt zero (b ∷ _) = BarData.barValue b
getValueAt (suc n) (_ ∷ bs) = getValueAt n bs

-- Get color at index
getColorAt : ℕ → List BarData → String
getColorAt _ [] = "#ccc"
getColorAt zero (b ∷ _) = showColor (BarData.barColor b)
getColorAt (suc n) (_ ∷ bs) = getColorAt n bs

-- Check if bar is highlighted (selected or hovered)
isHighlighted : ℕ → Model → Bool
isHighlighted idx m = (idx ≡ᵇ Model.selectedIdx m) ∨ (idx ≡ᵇ Model.hoveredIdx m)
  where
    _∨_ : Bool → Bool → Bool
    true ∨ _ = true
    false ∨ b = b

-- Render a single bar
renderBar : BarData × ℕ → ℕ → Node Model Msg
renderBar (bar , idx) _ =
  let xPos = toFloat idx *F (barWidth +F barGap) +F 50.0
      centerX = xPos +F barWidth ÷F 2.0
  in g (attr "cursor" "pointer"
       ∷ onClick (SelectBar idx)
       ∷ on "mouseenter" (HoverBar idx)
       ∷ on "mouseleave" LeaveBar
       ∷ attrBind "transform" (stringBinding λ m →
           if isHighlighted idx m
           then "translate(" ++ showFloat centerX ++ ",0) scale(1.05,1) translate(" ++ showFloat (0.0 -F centerX) ++ ",0)"
           else "")
       ∷ [])
       ( -- Bar rectangle
         rect' ( xF xPos
               ∷ attrBind "y" (stringBinding λ m →
                   let v = getValueAt idx (Model.bars m)
                       h = toFloat v *F (chartHeight ÷F maxValue)
                   in showFloat (chartHeight -F h))
               ∷ widthF barWidth
               ∷ attrBind "height" (stringBinding λ m →
                   let v = getValueAt idx (Model.bars m)
                   in showFloat (toFloat v *F (chartHeight ÷F maxValue)))
               ∷ fill_ (showColor (BarData.barColor bar))
               ∷ attrBind "stroke" (stringBinding λ m →
                   if idx ≡ᵇ Model.selectedIdx m then "#1e40af"
                   else if idx ≡ᵇ Model.hoveredIdx m then "#666"
                   else "none")
               ∷ attrBind "stroke-width" (stringBinding λ m →
                   if isHighlighted idx m then "2" else "0")
               ∷ attrBind "opacity" (stringBinding λ m →
                   if isHighlighted idx m then "1" else "0.75")
               ∷ rx_ "4"
               ∷ []) []
       ∷ -- Value label
         svgText ( xF (xPos +F barWidth ÷F 2.0)
                 ∷ attrBind "y" (stringBinding λ m →
                     let v = getValueAt idx (Model.bars m)
                         h = toFloat v *F (chartHeight ÷F maxValue)
                     in showFloat (chartHeight -F h -F 8.0))
                 ∷ textAnchor_ "middle"
                 ∷ fontSize_ "12"
                 ∷ fill_ "#333"
                 ∷ [])
           [ bind (stringBinding λ m → show (getValueAt idx (Model.bars m))) ]
       ∷ -- X-axis label
         svgText ( xF (xPos +F barWidth ÷F 2.0)
                 ∷ yF (chartHeight +F 20.0)
                 ∷ textAnchor_ "middle"
                 ∷ fontSize_ "12"
                 ∷ fill_ "#666"
                 ∷ [])
           [ text (BarData.barLabel bar) ]
       ∷ [] )

-- Y-axis with grid
yAxis : Node Model Msg
yAxis =
  g []
    ( -- Y-axis line
      line' (x1F 45.0 ∷ y1F 0.0 ∷ x2F 45.0 ∷ y2F chartHeight ∷ stroke_ "#ddd" ∷ []) []
    ∷ -- Grid lines and labels
      map (λ n →
        let yPos = chartHeight -F toFloat n *F (chartHeight ÷F maxValue)
        in g []
             ( line' ( x1F 45.0 ∷ y1F yPos
                     ∷ x2F chartWidth ∷ y2F yPos
                     ∷ stroke_ "#eee" ∷ []) []
             ∷ svgText ( xF 40.0 ∷ yF (yPos +F 4.0)
                       ∷ textAnchor_ "end"
                       ∷ fontSize_ "10"
                       ∷ fill_ "#999" ∷ [])
                 [ text (show n) ]
             ∷ [] ))
        (0 ∷ 25 ∷ 50 ∷ 75 ∷ 100 ∷ []) )

-- Controls
chartControls : Node Model Msg
chartControls =
  div (style "margin-top" "15px" ∷ style "display" "flex" ∷ style "gap" "10px" ∷ style "align-items" "center" ∷ style "justify-content" "center" ∷ [])
    ( span (style "color" "#666" ∷ [])
        [ bind (stringBinding λ m →
            if Model.selectedIdx m <ᵇ 900
            then "Selected: Bar " ++ show (Model.selectedIdx m)
            else "Click a bar to select") ]
    ∷ button (onClick SubSelected ∷ style "padding" "8px 16px" ∷ [])
        [ text "-10" ]
    ∷ button (onClick AddSelected ∷ style "padding" "8px 16px" ∷ [])
        [ text "+10" ]
    ∷ [] )

-- Main template
chartTemplate : Node Model Msg
chartTemplate =
  div (class "chart-demo" ∷ style "text-align" "center" ∷ [])
    ( h1 [] [ text "SVG Bar Chart" ]
    ∷ p (style "color" "#666" ∷ [])
        [ text "Click bars to select, use buttons or scroll wheel to modify" ]
    ∷ svg ( viewBox_ ("-5 -10 " ++ showFloat (chartWidth +F 10.0) ++ " " ++ showFloat (chartHeight +F 50.0))
          ∷ width_ (showFloat (chartWidth +F 60.0))
          ∷ height_ (showFloat (chartHeight +F 70.0))
          ∷ style "background" "#fafafa"
          ∷ style "border-radius" "8px"
          ∷ onSvgWheel WheelSelected
          ∷ [])
        ( -- Background rect to catch clicks on empty space
          rect' ( xF -5.0 ∷ yF -10.0
                ∷ widthF (chartWidth +F 10.0) ∷ heightF (chartHeight +F 50.0)
                ∷ fill_ "transparent"
                ∷ onClick Deselect
                ∷ []) []
        ∷ yAxis
        ∷ foreach (λ m → indexBars (Model.bars m)) renderBar
        ∷ [] )
    ∷ chartControls
    ∷ [] )

------------------------------------------------------------------------
-- App
------------------------------------------------------------------------

chartApp : ReactiveApp Model Msg
chartApp = simpleApp initModel updateModel chartTemplate

app : ReactiveApp Model Msg
app = chartApp
