{-# OPTIONS --without-K #-}

-- SvgDraggable: wrapper for draggable elements
-- Adds drag handles and visual feedback

module Agdelte.Svg.Controls.Draggable where

open import Data.String using (String; _++_)
open import Data.Float using (Float; _+_; _-_; _*_)
open import Data.Float.Base using (_÷_; _≤ᵇ_)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import Agdelte.Reactive.Node using (Node; Attr; elem; attr; attrBind; on; text; stringBinding)
open import Agdelte.Svg.Elements using (g; rect'; circle')
open import Agdelte.Svg.Attributes
  hiding (x_; y_)
  renaming (xF to attrX; yF to attrY; cxF to attrCx; cyF to attrCy)
open import Agdelte.Css.Show using (showFloat)

------------------------------------------------------------------------
-- Drag State
------------------------------------------------------------------------

record DragState : Set where
  constructor mkDragState
  field
    isDragging : Bool
    dragStartX : Float
    dragStartY : Float
    offsetX    : Float
    offsetY    : Float

open DragState public

initialDragState : DragState
initialDragState = mkDragState false 0.0 0.0 0.0 0.0

------------------------------------------------------------------------
-- Draggable Style
------------------------------------------------------------------------

record DraggableStyle : Set where
  constructor mkDraggableStyle
  field
    handleColor   : String    -- drag handle color
    handleSize    : Float     -- handle visual size
    hoverColor    : String    -- color when hovered
    activeColor   : String    -- color when dragging
    showHandles   : Bool      -- show corner handles

open DraggableStyle public

defaultDraggableStyle : DraggableStyle
defaultDraggableStyle = mkDraggableStyle
  "#3b82f6"    -- blue handles
  8.0          -- handle size
  "#60a5fa"    -- lighter blue hover
  "#2563eb"    -- darker blue active
  true         -- show handles

minimalDraggableStyle : DraggableStyle
minimalDraggableStyle = mkDraggableStyle
  "transparent"
  0.0
  "transparent"
  "transparent"
  false

------------------------------------------------------------------------
-- Drag Handle
------------------------------------------------------------------------

-- Single drag handle (corner circle)
svgDragHandle : ∀ {M Msg}
              → Float → Float       -- x, y
              → Float               -- size
              → String              -- color
              → Msg                 -- onMouseDown
              → Node M Msg
svgDragHandle px py size color msg =
  circle' ( attrCx px
          ∷ attrCy py
          ∷ rF (size ÷ 2.0)
          ∷ fill_ color
          ∷ attr "cursor" "move"
          ∷ on "mousedown" msg
          ∷ [] ) []

------------------------------------------------------------------------
-- Bounds clamping
------------------------------------------------------------------------

private
  clampFloat : Float → Float → Float → Float
  clampFloat lo hi v = if v ≤ᵇ lo then lo else if hi ≤ᵇ v then hi else v

  applyBound : Maybe (Float × Float) → Float → Float
  applyBound nothing v = v
  applyBound (just bounds) v = clampFloat (proj₁ bounds) (proj₂ bounds) v

------------------------------------------------------------------------
-- Draggable Container
------------------------------------------------------------------------

-- Wrap content to make it draggable
-- Shows selection box and corner handles when selected
-- getDragState: extracts DragState from model to adjust position and cursor
-- boundsX/boundsY: optional min/max clamping for rendered position
svgDraggable : ∀ {M Msg}
             → Float → Float → Float → Float  -- x, y, width, height
             → Bool                           -- isSelected
             → DraggableStyle
             → (M → DragState)                -- getDragState
             → Maybe (Float × Float)          -- boundsX (min, max)
             → Maybe (Float × Float)          -- boundsY (min, max)
             → Msg                            -- onSelect (click)
             → Msg                            -- onDragStart
             → List (Node M Msg)              -- children
             → Node M Msg
svgDraggable {M} px py w h selected sty getDragState boundsX boundsY onSelect onDrag children =
  let handleSz = handleSize sty
      handleClr = if selected then handleColor sty else "transparent"
      -- Compute clamped position from model's DragState
      posStr : M → String
      posStr m =
        let ds  = getDragState m
            rx  = applyBound boundsX (px + offsetX ds)
            ry  = applyBound boundsY (py + offsetY ds)
        in "translate(" ++ showFloat (rx - px) ++ "," ++ showFloat (ry - py) ++ ")"
      cursorStr : M → String
      cursorStr m = if isDragging (getDragState m) then "grabbing" else "move"
  -- Note: on "click" removed to disambiguate drag vs click.
  -- mousedown covers both: callers interpret mousedown-without-drag as select.
  in g ( attr "class" "svg-draggable"
       ∷ attrBind "cursor" (stringBinding cursorStr)
       ∷ on "mousedown" onDrag
       ∷ attrBind "transform" (stringBinding posStr)
       ∷ [] )
       ( -- Selection border (when selected)
         (if selected
          then rect' ( attrX (px - 2.0)
                     ∷ attrY (py - 2.0)
                     ∷ widthF (w + 4.0)
                     ∷ heightF (h + 4.0)
                     ∷ fill_ "none"
                     ∷ stroke_ (handleColor sty)
                     ∷ strokeWidthF 1.0
                     ∷ attr "stroke-dasharray" "4,4"
                     ∷ [] ) []
          else g [] [])
       -- Content
       ∷ g [] children
       -- Corner handles (when selected and enabled)
       ∷ (if selected Data.Bool.∧ showHandles sty
          then g [] ( svgDragHandle px py handleSz handleClr onDrag
                    ∷ svgDragHandle (px + w) py handleSz handleClr onDrag
                    ∷ svgDragHandle px (py + h) handleSz handleClr onDrag
                    ∷ svgDragHandle (px + w) (py + h) handleSz handleClr onDrag
                    ∷ [] )
          else g [] [])
       ∷ [] )
  where open import Data.Bool using (_∧_)

------------------------------------------------------------------------
-- Simple Draggable
------------------------------------------------------------------------

svgDraggableSimple : ∀ {M Msg}
                   → Float → Float → Float → Float
                   → Bool
                   → (M → DragState)
                   → Msg → Msg
                   → List (Node M Msg)
                   → Node M Msg
svgDraggableSimple px py w h selected getDragState onSelect onDrag children =
  svgDraggable px py w h selected defaultDraggableStyle getDragState nothing nothing onSelect onDrag children

------------------------------------------------------------------------
-- Move Handle Icon (4 arrows)
------------------------------------------------------------------------

svgMoveHandle : ∀ {M Msg}
              → Float → Float       -- center x, y
              → Float               -- size
              → String              -- color
              → Msg
              → Node M Msg
svgMoveHandle cx cy size color msg =
  let halfSz = size ÷ 2.0
      arrowLen = size * 0.3
  in g ( attr "class" "svg-move-handle"
       ∷ attr "cursor" "move"
       ∷ on "mousedown" msg
       ∷ [] )
       ( -- Background circle
         circle' ( attrCx cx
                 ∷ attrCy cy
                 ∷ rF halfSz
                 ∷ fill_ "white"
                 ∷ stroke_ color
                 ∷ strokeWidthF 1.0
                 ∷ [] ) []
       -- 4-arrow icon
       ∷ elem "path" ( d_ ( "M " ++ showFloat cx ++ " " ++ showFloat (cy - arrowLen)
                         ++ " L " ++ showFloat cx ++ " " ++ showFloat (cy + arrowLen)
                         ++ " M " ++ showFloat (cx - arrowLen) ++ " " ++ showFloat cy
                         ++ " L " ++ showFloat (cx + arrowLen) ++ " " ++ showFloat cy )
                     ∷ stroke_ color
                     ∷ strokeWidthF 1.5
                     ∷ fill_ "none"
                     ∷ attr "stroke-linecap" "round"
                     ∷ [] ) []
       ∷ [] )
