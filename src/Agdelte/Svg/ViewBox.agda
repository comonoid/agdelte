{-# OPTIONS --without-K #-}

-- SVG ViewBox Helpers
-- Typed viewBox with pan/zoom operations

module Agdelte.Svg.ViewBox where

open import Data.Float using (Float; _+_; _-_; _*_; _÷_)
open import Data.String using (String; _++_)
open import Agdelte.Css.Show using (showFloat)
open import Agdelte.Reactive.Node using (Attr; attr; attrBind; Binding; stringBinding)
open import Agdelte.Svg.Path using (Point; x; y; _,_)

------------------------------------------------------------------------
-- ViewBox type
------------------------------------------------------------------------

record ViewBox : Set where
  constructor mkViewBox
  field
    minX   : Float
    minY   : Float
    width  : Float
    height : Float

open ViewBox public

------------------------------------------------------------------------
-- Rendering
------------------------------------------------------------------------

showViewBox : ViewBox → String
showViewBox vb = showFloat (minX vb) ++ " " ++
                 showFloat (minY vb) ++ " " ++
                 showFloat (width vb) ++ " " ++
                 showFloat (height vb)

-- ViewBox as attribute
viewBox' : ∀ {M Msg} → ViewBox → Attr M Msg
viewBox' vb = attr "viewBox" (showViewBox vb)

-- Dynamic viewBox bound to model
viewBoxBind : ∀ {M Msg} → (M → ViewBox) → Attr M Msg
viewBoxBind f = attrBind "viewBox" (stringBinding (showViewBox ∘ f))
  where open import Function using (_∘_)

------------------------------------------------------------------------
-- ViewBox operations
------------------------------------------------------------------------

-- Pan viewBox by delta
panViewBox : Float → Float → ViewBox → ViewBox
panViewBox dx dy vb = mkViewBox
  (minX vb + dx)
  (minY vb + dy)
  (width vb)
  (height vb)

-- Pan by Point
panViewBoxPt : Point → ViewBox → ViewBox
panViewBoxPt p vb = panViewBox (x p) (y p) vb

-- Zoom viewBox around center (scale > 1 = zoom out, < 1 = zoom in)
zoomViewBox : Float → ViewBox → ViewBox
zoomViewBox scale vb =
  let
    cx = minX vb + width vb * 0.5
    cy = minY vb + height vb * 0.5
    newW = width vb * scale
    newH = height vb * scale
  in mkViewBox
    (cx - newW * 0.5)
    (cy - newH * 0.5)
    newW
    newH

-- Zoom around specific point in SVG coordinates
zoomViewBoxAt : Float → Point → ViewBox → ViewBox
zoomViewBoxAt scale p vb =
  let
    -- Point relative to viewBox
    relX = x p - minX vb
    relY = y p - minY vb
    -- New dimensions
    newW = width vb * scale
    newH = height vb * scale
    -- Keep point at same relative position
    newMinX = x p - relX * scale
    newMinY = y p - relY * scale
  in mkViewBox newMinX newMinY newW newH

-- Fit content with padding (assumes content at origin with given size)
fitContent : Float → Float → Float → ViewBox
fitContent contentW contentH padding =
  mkViewBox (0.0 - padding) (0.0 - padding) (contentW + padding * 2.0) (contentH + padding * 2.0)

-- Center viewBox on a point
centerOn : Point → ViewBox → ViewBox
centerOn p vb = mkViewBox
  (x p - width vb * 0.5)
  (y p - height vb * 0.5)
  (width vb)
  (height vb)

------------------------------------------------------------------------
-- PreserveAspectRatio
------------------------------------------------------------------------

-- Align options
data Align : Set where
  none : Align                    -- don't preserve aspect ratio
  xMinYMin xMidYMin xMaxYMin : Align
  xMinYMid xMidYMid xMaxYMid : Align
  xMinYMax xMidYMax xMaxYMax : Align

-- Meet vs Slice
data MeetOrSlice : Set where
  meet  : MeetOrSlice  -- scale to fit entirely (letterbox)
  slice : MeetOrSlice  -- scale to fill (crop)

showAlign : Align → String
showAlign none     = "none"
showAlign xMinYMin = "xMinYMin"
showAlign xMidYMin = "xMidYMin"
showAlign xMaxYMin = "xMaxYMin"
showAlign xMinYMid = "xMinYMid"
showAlign xMidYMid = "xMidYMid"
showAlign xMaxYMid = "xMaxYMid"
showAlign xMinYMax = "xMinYMax"
showAlign xMidYMax = "xMidYMax"
showAlign xMaxYMax = "xMaxYMax"

showMeetOrSlice : MeetOrSlice → String
showMeetOrSlice meet  = "meet"
showMeetOrSlice slice = "slice"

-- PreserveAspectRatio as attribute
preserveAspectRatio' : ∀ {M Msg} → Align → MeetOrSlice → Attr M Msg
preserveAspectRatio' a m = attr "preserveAspectRatio" (showAlign a ++ " " ++ showMeetOrSlice m)

-- Common preset: center, fit entirely
preserveAspectRatioCenter : ∀ {M Msg} → Attr M Msg
preserveAspectRatioCenter = attr "preserveAspectRatio" "xMidYMid meet"

-- No aspect ratio preservation (stretch to fill)
preserveAspectRatioNone : ∀ {M Msg} → Attr M Msg
preserveAspectRatioNone = attr "preserveAspectRatio" "none"

------------------------------------------------------------------------
-- Default viewBox
------------------------------------------------------------------------

-- Standard 100x100 viewBox (useful for scalable icons)
viewBox100 : ViewBox
viewBox100 = mkViewBox 0.0 0.0 100.0 100.0

-- Standard 0-1 normalized viewBox
viewBoxUnit : ViewBox
viewBoxUnit = mkViewBox 0.0 0.0 1.0 1.0
