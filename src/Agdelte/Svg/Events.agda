{-# OPTIONS --without-K #-}

-- SVG Event Helpers
-- Event handlers with SVG coordinate conversion
--
-- COORDINATE SYSTEMS:
--
-- SVG Coordinates (onSvgPointerDown, onSvgPointerMove, onSvgPointerUp):
--   - Coordinates in SVG user space (affected by viewBox)
--   - Use for: drawing, placing elements, hit testing within SVG
--   - Changes when viewBox changes (e.g., during pan/zoom)
--
-- Screen Coordinates (onScreenPointerDown, onScreenPointerMove, onScreenPointerUp):
--   - Raw pixel coordinates from the event (clientX, clientY)
--   - Use for: drag operations, gestures, UI interactions
--   - Stable regardless of SVG transformations
--
-- Example: For a pan/zoom SVG:
--   - Use Screen coords for drag delta calculation (stable reference)
--   - Use SVG coords to place new elements at cursor position

module Agdelte.Svg.Events where

open import Data.Float using (Float)
open import Data.String using (String)
open import Agdelte.Reactive.Node using (Attr; on; onValue; onValueScreen)
open import Agdelte.Svg.Path using (Point; _,_)

------------------------------------------------------------------------
-- Point message wrapper
------------------------------------------------------------------------

-- For events that return SVG coordinates
-- The runtime will extract x,y from the event and format as "x,y"
-- Use with onSvgPoint to parse back

postulate parsePointJS : String → Float → Float → (Float → Float → Point) → Point
{-# COMPILE JS parsePointJS = s => defX => defY => mk => {
  const parts = s.split(',');
  if (parts.length === 2) {
    const x = parseFloat(parts[0]);
    const y = parseFloat(parts[1]);
    if (!isNaN(x) && !isNaN(y)) return mk(x)(y);
    console.warn('parsePoint: invalid coordinates in "' + s + '", using defaults');
  } else if (s && s !== '0,0') {
    console.warn('parsePoint: malformed input "' + s + '", expected "x,y" format');
  }
  return mk(defX)(defY);
} #-}

parsePoint : String → Point
parsePoint s = parsePointJS s 0.0 0.0 _,_

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

-- Parse float from string
postulate parseFloatJS : String → Float
{-# COMPILE JS parseFloatJS = s => {
  const n = parseFloat(s);
  if (isNaN(n)) {
    if (s && s !== '0') console.warn('parseFloat: invalid number "' + s + '"');
    return 0;
  }
  return n;
} #-}

-- Returns delta as string "deltaY" (positive = zoom out, negative = zoom in)
onSvgWheel : ∀ {M Msg} → (Float → Msg) → Attr M Msg
onSvgWheel handler = onValue "wheel" (λ s → handler (parseFloatJS s))

------------------------------------------------------------------------
-- Screen coordinate events (for pan/drag - more stable than SVG coords)
------------------------------------------------------------------------

-- These use clientX/clientY directly (screen pixels)
-- Better for drag operations because viewBox changes don't affect them

onScreenPointerDown : ∀ {M Msg} → (Point → Msg) → Attr M Msg
onScreenPointerDown handler = onValueScreen "pointerdown" (λ s → handler (parsePoint s))

onScreenPointerMove : ∀ {M Msg} → (Point → Msg) → Attr M Msg
onScreenPointerMove handler = onValueScreen "pointermove" (λ s → handler (parsePoint s))

onScreenPointerUp : ∀ {M Msg} → (Point → Msg) → Attr M Msg
onScreenPointerUp handler = onValueScreen "pointerup" (λ s → handler (parsePoint s))
