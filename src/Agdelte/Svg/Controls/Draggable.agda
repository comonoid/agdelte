{-# OPTIONS --without-K #-}

-- SvgDraggable: wrapper for draggable elements
-- Adds drag handles and visual feedback

module Agdelte.Svg.Controls.Draggable where

open import Data.String using (String; _++_)
open import Data.Float using (Float; _+_; _-_; _*_)
open import Data.Float.Base using (_÷_)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; false; if_then_else_)

open import Agdelte.Reactive.Node using (Node; Attr; elem; attr; on; text)
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
-- Draggable Container
------------------------------------------------------------------------

-- Wrap content to make it draggable
-- Shows selection box and corner handles when selected
svgDraggable : ∀ {M Msg}
             → Float → Float → Float → Float  -- x, y, width, height
             → Bool                           -- isSelected
             → DraggableStyle
             → Msg                            -- onSelect (click)
             → Msg                            -- onDragStart
             → List (Node M Msg)              -- children
             → Node M Msg
svgDraggable px py w h selected sty onSelect onDrag children =
  let handleSz = handleSize sty
      handleClr = if selected then handleColor sty else "transparent"
  in g ( attr "class" "svg-draggable"
       ∷ attr "cursor" "move"
       ∷ on "click" onSelect
       ∷ on "mousedown" onDrag
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
                   → Bool → Msg → Msg
                   → List (Node M Msg)
                   → Node M Msg
svgDraggableSimple px py w h selected onSelect onDrag children =
  svgDraggable px py w h selected defaultDraggableStyle onSelect onDrag children

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
