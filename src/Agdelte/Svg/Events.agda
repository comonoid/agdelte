{-# OPTIONS --without-K #-}

-- SVG Event Helpers
-- Event handlers with SVG coordinate conversion

module Agdelte.Svg.Events where

open import Data.Float using (Float)
open import Data.String using (String)
open import Agdelte.Reactive.Node using (Attr; on; onValue)
open import Agdelte.Svg.Path using (Point; _,_)

------------------------------------------------------------------------
-- Point message wrapper
------------------------------------------------------------------------

-- For events that return SVG coordinates
-- The runtime will extract x,y from the event and format as "x,y"
-- Use with onSvgPoint to parse back

parsePoint : String → Point
parsePoint s = x' , y'
  where
    postulate parsePointJS : String → Float → Float → (Float → Float → Point) → Point
    {-# COMPILE JS parsePointJS = (s, defX, defY, mk) => {
      const parts = s.split(',');
      if (parts.length === 2) {
        const x = parseFloat(parts[0]);
        const y = parseFloat(parts[1]);
        if (!isNaN(x) && !isNaN(y)) return mk(x)(y);
      }
      return mk(defX)(defY);
    } #-}
    x' = 0.0
    y' = 0.0
    -- Note: actual parsing happens via onSvgPoint in runtime

------------------------------------------------------------------------
-- SVG Click with coordinates
------------------------------------------------------------------------

-- Click handler that receives SVG coordinates
-- Runtime converts screen coords to SVG coords via getScreenCTM().inverse()
onSvgClick : ∀ {M Msg} → (Point → Msg) → Attr M Msg
onSvgClick handler = onValue "click" (λ s → handler (parsePoint s))

-- Double-click with SVG coordinates
onSvgDblClick : ∀ {M Msg} → (Point → Msg) → Attr M Msg
onSvgDblClick handler = onValue "dblclick" (λ s → handler (parsePoint s))

------------------------------------------------------------------------
-- Pointer events (unified mouse/touch/pen)
------------------------------------------------------------------------

onSvgPointerDown : ∀ {M Msg} → (Point → Msg) → Attr M Msg
onSvgPointerDown handler = onValue "pointerdown" (λ s → handler (parsePoint s))

onSvgPointerMove : ∀ {M Msg} → (Point → Msg) → Attr M Msg
onSvgPointerMove handler = onValue "pointermove" (λ s → handler (parsePoint s))

onSvgPointerUp : ∀ {M Msg} → (Point → Msg) → Attr M Msg
onSvgPointerUp handler = onValue "pointerup" (λ s → handler (parsePoint s))

onSvgPointerEnter : ∀ {M Msg} → (Point → Msg) → Attr M Msg
onSvgPointerEnter handler = onValue "pointerenter" (λ s → handler (parsePoint s))

onSvgPointerLeave : ∀ {M Msg} → Msg → Attr M Msg
onSvgPointerLeave msg = on "pointerleave" msg

------------------------------------------------------------------------
-- Mouse events (when you need mouse-specific behavior)
------------------------------------------------------------------------

onSvgMouseDown : ∀ {M Msg} → (Point → Msg) → Attr M Msg
onSvgMouseDown handler = onValue "mousedown" (λ s → handler (parsePoint s))

onSvgMouseMove : ∀ {M Msg} → (Point → Msg) → Attr M Msg
onSvgMouseMove handler = onValue "mousemove" (λ s → handler (parsePoint s))

onSvgMouseUp : ∀ {M Msg} → (Point → Msg) → Attr M Msg
onSvgMouseUp handler = onValue "mouseup" (λ s → handler (parsePoint s))

------------------------------------------------------------------------
-- Wheel event (for zoom)
------------------------------------------------------------------------

-- Returns delta as string "deltaY" (positive = zoom out, negative = zoom in)
onSvgWheel : ∀ {M Msg} → (Float → Msg) → Attr M Msg
onSvgWheel handler = onValue "wheel" (λ s → handler (parseFloat s))
  where
    postulate parseFloat : String → Float
    {-# COMPILE JS parseFloat = s => parseFloat(s) || 0 #-}
