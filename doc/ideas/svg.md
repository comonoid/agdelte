# SVG as first-class typed DSL

## Current state

The `Node` type uses a string tag name:

```agda
elem : String → List (Attr Model Msg) → List (Node Model Msg) → Node Model Msg
```

So SVG elements are already expressible:

```agda
elem "svg" (attr "viewBox" "0 0 100 100" ∷ [])
  (elem "circle" (attr "cx" "50" ∷ attr "cy" "50" ∷ attr "r" "40" ∷ []) []
  ∷ [])
```

This compiles, but **doesn't render** because the runtime creates elements with
`document.createElement(tag)` instead of `document.createElementNS(ns, tag)`.
SVG elements in the HTML namespace are inert -- the browser ignores them.

## Phase 0: Namespace-aware renderer

The only blocking change. Not SVG-specific -- a general improvement to the
renderer that enables SVG, MathML, and any future XML namespace.

### The problem

Both renderers (`reactive.js:358`, `dom.js:83`) use `document.createElement(tag)`
unconditionally. This creates all elements in the HTML namespace. For HTML
content this is correct (HTML namespace is the default). But SVG elements
created with `createElement` are inert -- the browser ignores them. SVG
requires `document.createElementNS('http://www.w3.org/2000/svg', tag)`.

### How browsers handle it

The browser's HTML parser uses **context-based namespace propagation**:
- Start in HTML namespace (default)
- `<svg>` switches to SVG namespace
- `<math>` switches to MathML namespace
- All children inherit the current namespace
- `<foreignObject>` (inside SVG) switches back to HTML namespace
- `<annotation-xml>` (inside MathML) switches back to HTML namespace

No tag lists. No ambiguity with tags like `<a>` that exist in both HTML
and SVG. The runtime should work the same way.

### reactive.js (reactive renderer)

The reactive renderer already has `currentScope` -- a global variable with
save/modify/restore pattern during tree traversal. `currentNs` follows
the exact same pattern:

```javascript
const SVG_NS = 'http://www.w3.org/2000/svg';
let currentNs = null;  // null = HTML namespace (use createElement)

// In renderNode:
elem: (tag, attrs, children) => {
  const prevNs = currentNs;

  // Entering namespace
  if (tag === 'svg') currentNs = SVG_NS;
  // (future: if (tag === 'math') currentNs = MATHML_NS;)

  // Create element in current namespace
  const el = currentNs
    ? document.createElementNS(currentNs, tag)
    : document.createElement(tag);

  // Exiting namespace (children go back to HTML)
  if (tag === 'foreignObject') currentNs = null;

  const attrArray = listToArray(attrs);
  for (const attr of attrArray) {
    applyAttr(el, attr);
  }

  const childArray = listToArray(children);
  for (const child of childArray) {
    const childNode = renderNode(child);
    if (childNode) el.appendChild(childNode);
  }

  currentNs = prevNs;  // restore after subtree
  return el;
}
```

`when` and `foreach` also call `renderNode` recursively -- they automatically
inherit `currentNs` from the parent context (same as `currentScope`).

Existing HTML examples work identically: `currentNs` stays `null` throughout,
`createElement` path is taken. Zero impact on existing code.

### dom.js (VirtualDOM renderer)

The VirtualDOM renderer has no global context. Thread `ns` as a parameter:

```javascript
export function createElement(vnode, dispatch, ns = null) {
  // ...
  const { tag } = vnode;

  if (tag === 'svg') ns = SVG_NS;

  const el = ns
    ? document.createElementNS(ns, tag)
    : document.createElement(tag);

  const childNs = (tag === 'foreignObject') ? null : ns;

  for (const child of children) {
    el.appendChild(createElement(child, dispatch, childNs));
  }
  return el;
}
```

The `patch` function also needs namespace awareness when replacing elements
(tag mismatch → create new element). Currently `patch` calls `createElement`,
so the `ns` parameter propagates naturally.

### Namespaced attributes

SVG uses `xlink:href` and `xml:lang`. These need `setAttributeNS`:

```javascript
const ATTR_NS = {
  'xlink:href': 'http://www.w3.org/1999/xlink',
  'xlink:title': 'http://www.w3.org/1999/xlink',
  'xml:lang': 'http://www.w3.org/XML/1998/namespace',
  'xml:space': 'http://www.w3.org/XML/1998/namespace',
};

function setAttr(el, name, value) {
  const ns = ATTR_NS[name];
  if (ns) {
    el.setAttributeNS(ns, name, value);
  } else {
    el.setAttribute(name, value);
  }
}
```

This is a small map of 4 entries (not a tag list). `xlink:href` is
deprecated in SVG 2 (plain `href` works), but needed for compatibility.

### Scope of change

| File | Lines changed | What |
|------|--------------|------|
| `reactive.js` | ~8 | `currentNs` variable + save/restore in `elem` |
| `dom.js` | ~6 | `ns` parameter in `createElement` + `patch` |
| `dom.js` or shared | ~8 | `ATTR_NS` map + `setAttr` function |

Total: ~22 lines. No new files. No changes to Agda code. All existing
examples continue to work unchanged.

After Phase 0, bare `elem "circle"` inside `elem "svg"` renders correctly.
Everything below builds on top of this foundation.

## Phase 1: SVG element constructors

Smart constructors in `Agdelte.Svg.Elements`. Same pattern as `div`, `span`, `button`:

```agda
module Agdelte.Svg.Elements where

open import Agdelte.Reactive.Node

-- Container elements (attrs + children)
svg : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
svg = elem "svg"

g : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
g = elem "g"

defs : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
defs = elem "defs"

symbol' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
symbol' = elem "symbol"

marker' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
marker' = elem "marker"

clipPath' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
clipPath' = elem "clipPath"

mask' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
mask' = elem "mask"

pattern' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
pattern' = elem "pattern"

-- Shapes (attrs only, no children)
circle' : ∀ {M Msg} → List (Attr M Msg) → Node M Msg
circle' as = elem "circle" as []

rect' : ∀ {M Msg} → List (Attr M Msg) → Node M Msg
rect' as = elem "rect" as []

ellipse' : ∀ {M Msg} → List (Attr M Msg) → Node M Msg
ellipse' as = elem "ellipse" as []

line' : ∀ {M Msg} → List (Attr M Msg) → Node M Msg
line' as = elem "line" as []

polyline' : ∀ {M Msg} → List (Attr M Msg) → Node M Msg
polyline' as = elem "polyline" as []

polygon' : ∀ {M Msg} → List (Attr M Msg) → Node M Msg
polygon' as = elem "polygon" as []

path' : ∀ {M Msg} → List (Attr M Msg) → Node M Msg
path' as = elem "path" as []

-- Text elements (attrs + children for tspan nesting)
svgText : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
svgText = elem "text"

tspan' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
tspan' = elem "tspan"

textPath' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
textPath' = elem "textPath"

-- Gradients
linearGradient' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
linearGradient' = elem "linearGradient"

radialGradient' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
radialGradient' = elem "radialGradient"

stop' : ∀ {M Msg} → List (Attr M Msg) → Node M Msg
stop' as = elem "stop" as []

-- Filters
filter' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
filter' = elem "filter"

feGaussianBlur' : ∀ {M Msg} → List (Attr M Msg) → Node M Msg
feGaussianBlur' as = elem "feGaussianBlur" as []

feOffset' : ∀ {M Msg} → List (Attr M Msg) → Node M Msg
feOffset' as = elem "feOffset" as []

feBlend' : ∀ {M Msg} → List (Attr M Msg) → Node M Msg
feBlend' as = elem "feBlend" as []

feColorMatrix' : ∀ {M Msg} → List (Attr M Msg) → Node M Msg
feColorMatrix' as = elem "feColorMatrix" as []

feMerge' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
feMerge' = elem "feMerge"

feMergeNode' : ∀ {M Msg} → List (Attr M Msg) → Node M Msg
feMergeNode' as = elem "feMergeNode" as []

-- Embedding
image' : ∀ {M Msg} → List (Attr M Msg) → Node M Msg
image' as = elem "image" as []

use' : ∀ {M Msg} → List (Attr M Msg) → Node M Msg
use' as = elem "use" as []

foreignObject' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
foreignObject' = elem "foreignObject"
```

Usage:

```agda
open import Agdelte.Svg.Elements

myIcon : Node Model Msg
myIcon =
  svg (attr "viewBox" "0 0 24 24" ∷ attr "width" "24" ∷ [])
    ( path' (attr "d" "M12 2L2 7l10 5 10-5-10-5z" ∷ attr "fill" "currentColor" ∷ [])
    ∷ [])
```

## Phase 2: SVG attribute helpers

From `Agdelte.Svg.Attributes`. Return `Attr Model Msg`.

### Geometry

```agda
-- Positioning
x_ y_ : ∀ {M Msg} → String → Attr M Msg
x_ = attr "x"
y_ = attr "y"

cx_ cy_ : ∀ {M Msg} → String → Attr M Msg
cx_ = attr "cx"
cy_ = attr "cy"

-- Dimensions
width_ height_ : ∀ {M Msg} → String → Attr M Msg
width_ = attr "width"
height_ = attr "height"

r_ : ∀ {M Msg} → String → Attr M Msg
r_ = attr "r"

rx_ ry_ : ∀ {M Msg} → String → Attr M Msg
rx_ = attr "rx"
ry_ = attr "ry"

-- Line endpoints
x1_ y1_ x2_ y2_ : ∀ {M Msg} → String → Attr M Msg
x1_ = attr "x1"
y1_ = attr "y1"
x2_ = attr "x2"
y2_ = attr "y2"

-- Polygon/polyline
points_ : ∀ {M Msg} → String → Attr M Msg
points_ = attr "points"

-- Path
d_ : ∀ {M Msg} → String → Attr M Msg
d_ = attr "d"

-- ViewBox
viewBox_ : ∀ {M Msg} → String → Attr M Msg
viewBox_ = attr "viewBox"
```

### Presentation

```agda
-- Fill & stroke
fill_ stroke_ : ∀ {M Msg} → String → Attr M Msg
fill_ = attr "fill"
stroke_ = attr "stroke"

strokeWidth_ : ∀ {M Msg} → String → Attr M Msg
strokeWidth_ = attr "stroke-width"

fillOpacity_ strokeOpacity_ opacity_ : ∀ {M Msg} → String → Attr M Msg
fillOpacity_ = attr "fill-opacity"
strokeOpacity_ = attr "stroke-opacity"
opacity_ = attr "opacity"

strokeDasharray_ strokeDashoffset_ : ∀ {M Msg} → String → Attr M Msg
strokeDasharray_ = attr "stroke-dasharray"
strokeDashoffset_ = attr "stroke-dashoffset"

strokeLinecap_ strokeLinejoin_ : ∀ {M Msg} → String → Attr M Msg
strokeLinecap_ = attr "stroke-linecap"
strokeLinejoin_ = attr "stroke-linejoin"

fillRule_ : ∀ {M Msg} → String → Attr M Msg
fillRule_ = attr "fill-rule"

-- Transform
transform_ : ∀ {M Msg} → String → Attr M Msg
transform_ = attr "transform"

-- References
href_ : ∀ {M Msg} → String → Attr M Msg
href_ = attr "href"

-- Markers
markerStart_ markerMid_ markerEnd_ : ∀ {M Msg} → String → Attr M Msg
markerStart_ = attr "marker-start"
markerMid_ = attr "marker-mid"
markerEnd_ = attr "marker-end"

-- Filter
filter_ : ∀ {M Msg} → String → Attr M Msg
filter_ = attr "filter"

-- Clip
clipPath_ : ∀ {M Msg} → String → Attr M Msg
clipPath_ = attr "clip-path"

-- Gradient stops
offset_ : ∀ {M Msg} → String → Attr M Msg
offset_ = attr "offset"

stopColor_ stopOpacity_ : ∀ {M Msg} → String → Attr M Msg
stopColor_ = attr "stop-color"
stopOpacity_ = attr "stop-opacity"
```

### Typed attribute constructors

Reuse `Length`, `Color` from CSS module:

```agda
open import Agdelte.Css.Length (Length; showLength)
open import Agdelte.Css.Color (Color; showColor)

-- Typed fill/stroke with Color
fillC : ∀ {M Msg} → Color → Attr M Msg
fillC c = attr "fill" (showColor c)

strokeC : ∀ {M Msg} → Color → Attr M Msg
strokeC c = attr "stroke" (showColor c)

-- Typed dimensions with Float
cxF cyF rF : ∀ {M Msg} → Float → Attr M Msg
cxF v = attr "cx" (showFloat v)
cyF v = attr "cy" (showFloat v)
rF v = attr "r" (showFloat v)

widthF heightF : ∀ {M Msg} → Float → Attr M Msg
widthF v = attr "width" (showFloat v)
heightF v = attr "height" (showFloat v)
```

### Text attributes and helpers

SVG text has no automatic line wrapping. Each line requires manual `<tspan>`
positioning. Text attributes:

```agda
-- Text positioning
textAnchor_ : ∀ {M Msg} → String → Attr M Msg   -- "start", "middle", "end"
textAnchor_ = attr "text-anchor"

dominantBaseline_ : ∀ {M Msg} → String → Attr M Msg  -- "auto", "middle", "hanging"
dominantBaseline_ = attr "dominant-baseline"

dx_ dy_ : ∀ {M Msg} → String → Attr M Msg   -- offset (single value or space-separated list)
dx_ = attr "dx"
dy_ = attr "dy"

textLength_ : ∀ {M Msg} → String → Attr M Msg
textLength_ = attr "textLength"

lengthAdjust_ : ∀ {M Msg} → String → Attr M Msg  -- "spacing", "spacingAndGlyphs"
lengthAdjust_ = attr "lengthAdjust"
```

**Multi-line text helper** (generates `<tspan>` chain):

```agda
-- In Agdelte.Svg.Text
multilineText : ∀ {M Msg} → Float → Float → String → List String → Node M Msg
multilineText x y lineHeight lines =
  svgText (x_ (showF x) ∷ y_ (showF y) ∷ [])
    (zipWithIndex (λ line i →
      tspan' ( attr "x" (showF x)
             ∷ (if i == 0 then [] else attr "dy" lineHeight ∷ []))
        (text line ∷ []))
    lines)
```

**Text on path:**

```agda
-- Text following a curve (requires <defs> path with id)
textOnPath : ∀ {M Msg} → String → String → List (Attr M Msg) → Node M Msg
textOnPath pathId content attrs =
  svgText attrs
    ( textPath' (href_ ("#" ++ pathId) ∷ []) (text content ∷ [])
    ∷ [])
```

**Text measurement** requires the DOM — `getComputedTextLength()` can't be
computed in Agda. Auto-sizing text boxes or justified text need a runtime
measurement command:

```agda
-- New Cmd variant (future):
measureText : String → (Float → Msg) → Cmd Msg
-- Runtime calls el.getComputedTextLength(), sends result as Msg
```

## Phase 3: Typed path DSL

The `d` attribute is a mini-language: `"M 10 20 L 30 40 C 50 60 70 80 90 100 Z"`.
Typos are silent. This is the highest-value typed DSL.

### Path commands

```agda
module Agdelte.Svg.Path where

-- A point in 2D space
record Point : Set where
  constructor _,_
  field x y : Float

data PathCmd : Set where
  -- Absolute commands
  M  : Point → PathCmd                              -- moveTo
  L  : Point → PathCmd                              -- lineTo
  H  : Float → PathCmd                              -- horizontal line
  V  : Float → PathCmd                              -- vertical line
  C  : Point → Point → Point → PathCmd              -- cubic bezier
  S  : Point → Point → PathCmd                      -- smooth cubic
  Q  : Point → Point → PathCmd                      -- quadratic bezier
  T  : Point → PathCmd                              -- smooth quadratic
  A  : Float → Float → Float → Bool → Bool → Point → PathCmd  -- arc
  Z  : PathCmd                                       -- closePath
  -- Relative commands
  m  : Point → PathCmd
  l  : Point → PathCmd
  h  : Float → PathCmd
  v  : Float → PathCmd
  c  : Point → Point → Point → PathCmd
  s  : Point → Point → PathCmd
  q  : Point → Point → PathCmd
  t  : Point → PathCmd
  a  : Float → Float → Float → Bool → Bool → Point → PathCmd

Path : Set
Path = List PathCmd

showCmd : PathCmd → String
showCmd (M p)              = "M" ++ showF (x p) ++ " " ++ showF (y p)
showCmd (L p)              = "L" ++ showF (x p) ++ " " ++ showF (y p)
showCmd (H x)              = "H" ++ showF x
showCmd (V y)              = "V" ++ showF y
showCmd (C c1 c2 p)        = "C" ++ showPt c1 ++ " " ++ showPt c2 ++ " " ++ showPt p
showCmd (S c2 p)           = "S" ++ showPt c2 ++ " " ++ showPt p
showCmd (Q c p)            = "Q" ++ showPt c ++ " " ++ showPt p
showCmd (T p)              = "T" ++ showPt p
showCmd (A rx ry rot large sweep p) =
  "A" ++ showF rx ++ " " ++ showF ry ++ " " ++ showF rot
      ++ " " ++ flag large ++ " " ++ flag sweep
      ++ " " ++ showPt p
showCmd Z                  = "Z"
-- ... relative commands similarly with lowercase letters

renderPath : Path → String
renderPath = intercalate " " ∘ map showCmd
```

### Usage

```agda
-- Triangle
triangle : Path
triangle = M (0.0 , 100.0) ∷ L (50.0 , 0.0) ∷ L (100.0 , 100.0) ∷ Z ∷ []

-- In template:
path' (d_ (renderPath triangle) ∷ fillC (hex "#4a9eff") ∷ [])
```

### Path combinators

```agda
-- Translate all points in a path
translatePath : Float → Float → Path → Path

-- Scale all points
scalePath : Float → Float → Path → Path

-- Reverse path direction (for cut-outs, winding)
reversePath : Path → Path

-- Concatenate paths
_<+>_ : Path → Path → Path
p1 <+> p2 = p1 ++ adjustStart p2
  where adjustStart replaces the first M with L if paths are joined

-- Close a path (ensure Z at end)
closePath : Path → Path

-- Estimate total path length (exact for L/H/V, approximate for C/Q/A)
pathLength : Path → Float
-- Uses line segment lengths directly, subdivides curves into N segments
-- Pure function — evaluated at compile time for static paths
```

### Path generators (compile-time)

Mathematical curves computed by Agda at compile time:

```agda
-- Regular polygon: n sides, radius r, center c
regularPolygon : ℕ → Float → Point → Path

-- Star polygon: n points, outer/inner radii
star : ℕ → Float → Float → Point → Path

-- Circle approximation (4 cubic beziers)
circleApprox : Float → Point → Path

-- Arc between two angles
arcPath : Float → Float → Float → Point → Path

-- Rounded rectangle
roundRect : Float → Float → Float → Float → Float → Path
roundRect x y w h r = ...

-- Sine wave (n samples)
sineWave : ℕ → Float → Float → Float → Path

-- Spiral
spiral : ℕ → Float → Float → Float → Point → Path
```

Since these are pure functions, the Agda compiler evaluates them at compile
time. The result is a `Path` value baked into the JS output. Zero runtime
cost for complex geometry.

```agda
-- A 5-pointed star, evaluated at compile time
myStar : String
myStar = renderPath (star 5 50.0 20.0 (50.0 , 50.0))
-- = "M50 0 L59.0 34.5 L97.5 34.5 L65.4 55.9 ..."
```

## Phase 4: Typed transforms

SVG `transform` is another mini-language: `"translate(10,20) rotate(45) scale(2)"`.

```agda
module Agdelte.Svg.Transform where

data Transform : Set where
  translate : Float → Float → Transform
  rotate    : Float → Transform                 -- degrees
  rotateAt  : Float → Float → Float → Transform -- degrees, cx, cy
  scale     : Float → Float → Transform
  scaleU    : Float → Transform                 -- uniform
  skewX     : Float → Transform
  skewY     : Float → Transform
  matrix    : Float → Float → Float → Float → Float → Float → Transform

showTransform : Transform → String
showTransform (translate tx ty) = "translate(" ++ showF tx ++ "," ++ showF ty ++ ")"
showTransform (rotate deg)      = "rotate(" ++ showF deg ++ ")"
showTransform (scaleU s)        = "scale(" ++ showF s ++ ")"
-- ...

renderTransforms : List Transform → String
renderTransforms = intercalate " " ∘ map showTransform
```

Usage:

```agda
g (transform_ (renderTransforms (translate 50.0 50.0 ∷ rotate 45.0 ∷ [])) ∷ [])
  ( rect' (x_ "-25" ∷ y_ "-25" ∷ width_ "50" ∷ height_ "50" ∷ [])
  ∷ [])
```

### Reactive transforms with Spring/Tween

```agda
-- Model stores spring-driven rotation
record Model : Set where
  field angle : Spring

-- Bind transform to spring position
attrBind "transform"
  (stringBinding λ m →
    renderTransforms (rotate (position (angle m)) ∷ []))
```

## Phase 5: Typed viewBox

```agda
record ViewBox : Set where
  constructor mkViewBox
  field
    minX   : Float
    minY   : Float
    width  : Float
    height : Float

showViewBox : ViewBox → String
showViewBox vb = showF (minX vb) ++ " " ++ showF (minY vb)
              ++ " " ++ showF (width vb) ++ " " ++ showF (height vb)

-- Compute aspect ratio
aspect : ViewBox → Float
aspect vb = width vb / height vb

-- Zoom: shrink viewBox around center
zoomViewBox : Float → ViewBox → ViewBox
zoomViewBox factor vb =
  let cx = minX vb + width vb / 2.0
      cy = minY vb + height vb / 2.0
      w' = width vb / factor
      h' = height vb / factor
  in mkViewBox (cx - w' / 2.0) (cy - h' / 2.0) w' h'

-- Pan: shift viewBox
panViewBox : Float → Float → ViewBox → ViewBox
panViewBox dx dy vb = record vb { minX = minX vb + dx ; minY = minY vb + dy }
```

### preserveAspectRatio

Controls how SVG content is scaled within the viewport:

```agda
data Align : Set where
  none : Align
  xMinYMin xMidYMin xMaxYMin : Align
  xMinYMid xMidYMid xMaxYMid : Align
  xMinYMax xMidYMax xMaxYMax : Align

data MeetOrSlice : Set where
  meet slice : MeetOrSlice

showPAR : Align → MeetOrSlice → String
showPAR none _     = "none"
showPAR align mos  = showAlign align ++ " " ++ showMOS mos

-- Typed preserveAspectRatio attribute
par_ : ∀ {M Msg} → Align → MeetOrSlice → Attr M Msg
par_ a m = attr "preserveAspectRatio" (showPAR a m)
```

Interactive pan+zoom with springs:

```agda
record Model : Set where
  field
    viewBox : ViewBox
    panX    : Spring
    panY    : Spring
    zoom    : Spring

-- Bind viewBox to spring-driven pan/zoom
attrBind "viewBox"
  (stringBinding λ m →
    showViewBox (zoomViewBox (position (zoom m))
      (panViewBox (position (panX m)) (position (panY m)) (viewBox m))))
```

## Phase 6: Reactive SVG (data visualization)

Agdelte's reactive bindings apply to SVG attributes. This enables
live-updating charts and visualizations with zero overhead.

### Bar chart

```agda
record BarData : Set where
  field label : String ; value : Float ; color : Color

barChart : (Model → List BarData) → Float → Float → Node Model Msg
barChart getData w h =
  svg (viewBox_ (showViewBox (mkViewBox 0.0 0.0 w h)) ∷ [])
    ( foreach getData (λ bar i →
        g (transform_ (renderTransforms
            (translate (toFloat i * barW + gap) 0.0 ∷ [])) ∷ [])
          ( rect' ( x_ "0"
                  ∷ attrBind "y" (stringBinding λ _ → showF (h - value bar * scale))
                  ∷ width_ (showF barW)
                  ∷ attrBind "height" (stringBinding λ _ → showF (value bar * scale))
                  ∷ fillC (color bar)
                  ∷ [])
          ∷ svgText (y_ (showF (h + 14.0))
                    ∷ attr "text-anchor" "middle"
                    ∷ [])
              (text (label bar) ∷ [])
          ∷ []))
    ∷ [])
```

### Line chart with path binding

```agda
lineChart : (Model → List Float) → Node Model Msg
lineChart getValues =
  svg (viewBox_ "0 0 300 200" ∷ [])
    ( path' ( attrBind "d" (stringBinding λ m →
                renderPath (dataToPath (getValues m) 300.0 200.0))
            ∷ stroke_ "#4a9eff"
            ∷ fill_ "none"
            ∷ strokeWidth_ "2"
            ∷ [])
    ∷ [])

dataToPath : List Float → Float → Float → Path
dataToPath [] _ _ = []
dataToPath (v ∷ []) _ h = M (0.0 , h - v) ∷ []
dataToPath (v ∷ vs) w h =
  let step = w / toFloat (length vs)
      pts  = zipWithIndex (λ val i → (toFloat i * step , h - val)) (v ∷ vs)
  in M (proj₁ (head pts)) ∷ map (λ p → L p) (tail pts)
```

`attrBind "d"` creates a reactive binding on the path data. When the model
changes, the runtime re-evaluates the path string and updates the single
DOM attribute. No VDOM diff, no tree rebuild -- O(1) attribute set.

### Pie chart

```agda
pieSector : Float → Float → Float → Float → Color → Node Model Msg
pieSector cx cy r startAngle endAngle color =
  let x1 = cx + r * cos startAngle
      y1 = cy + r * sin startAngle
      x2 = cx + r * cos endAngle
      y2 = cy + r * sin endAngle
      large = endAngle - startAngle > pi
  in path' ( d_ (renderPath (
               M (cx , cy)
             ∷ L (x1 , y1)
             ∷ A r r 0.0 large false (x2 , y2)
             ∷ Z ∷ []))
           ∷ fillC color ∷ [])
```

### foreach for data-driven elements

```agda
-- Scatter plot: one circle per data point
scatterPlot : (Model → List DataPoint) → Node Model Msg
scatterPlot getData =
  svg (viewBox_ "0 0 400 300" ∷ [])
    ( foreach getData (λ pt _ →
        circle' ( cxF (dataX pt * scaleX)
                ∷ cyF (300.0 - dataY pt * scaleY)
                ∷ rF 4.0
                ∷ fillC (categoryColor (category pt))
                ∷ on "click" (SelectPoint (pointId pt))
                ∷ []))
    ∷ [])
```

`foreach` + SVG = data-driven visualization with automatic DOM reconciliation.
Add a data point → one `<circle>` added. Remove one → one `<circle>` removed.
No full re-render.

### HTML inside SVG (`<foreignObject>`)

`<foreignObject>` embeds full HTML content inside SVG coordinate space.
Context-based namespacing (Phase 0) handles this automatically:
`foreignObject` children are created with `createElement` (HTML).

The key use case: **rich tooltips** in data visualizations:

```agda
-- HTML tooltip positioned in SVG coordinate space
tooltip : (Model → Bool) → (Model → Float) → (Model → Float) → Node Model Msg
tooltip isVisible getX getY =
  when isVisible
    (foreignObject' ( attrBind "x" (stringBinding λ m → showF (getX m))
                    ∷ attrBind "y" (stringBinding λ m → showF (getY m))
                    ∷ width_ "200" ∷ height_ "120" ∷ [])
      ( div (class' "chart-tooltip" ∷ [])
          ( h3 [] (bindF (λ m → pointLabel m) ∷ [])
          ∷ p [] (bindF (λ m → "Value: " ++ showF (pointValue m)) ∷ [])
          ∷ [])
      ∷ []))
```

CSS styling works normally on HTML content inside `foreignObject` — use
`Stylesheet` for tooltip styles. The HTML sub-tree is a full Agdelte
component: `bindF`, `on`, `when`, `foreach` all work inside it.

This bridges SVG (positioning, coordinate transforms) and HTML (rich
text, forms, complex layouts) seamlessly.

## Phase 7: Defs-based resources (gradients, filters, clips, patterns, markers)

### Gradients

```agda
module Agdelte.Svg.Gradient where

record GradientStop : Set where
  constructor mkStop
  field
    offset : Float        -- 0.0 to 1.0
    color  : Color
    opacity : Float       -- 0.0 to 1.0

data GradientDir : Set where
  horizontal vertical : GradientDir
  diagonal : Float → Float → Float → Float → GradientDir  -- x1 y1 x2 y2

renderGradient : String → GradientDir → List GradientStop → Node Model Msg
renderGradient id dir stops =
  linearGradient' (attr "id" id ∷ dirAttrs dir)
    (map renderStop stops)
  where
    dirAttrs horizontal = x1_ "0%" ∷ y1_ "0%" ∷ x2_ "100%" ∷ y2_ "0%" ∷ []
    dirAttrs vertical   = x1_ "0%" ∷ y1_ "0%" ∷ x2_ "0%" ∷ y2_ "100%" ∷ []
    -- ...
    renderStop s = stop' ( offset_ (showPct (offset s))
                         ∷ stopColor_ (showColor (color s))
                         ∷ stopOpacity_ (showF (opacity s)) ∷ [])
```

Usage:

```agda
defs []
  ( renderGradient "sky" vertical
      ( mkStop 0.0 (hex "#87CEEB") 1.0
      ∷ mkStop 1.0 (hex "#E0F7FA") 1.0
      ∷ [])
  ∷ [])
-- Reference: fill_ "url(#sky)"
```

### Filters

```agda
module Agdelte.Svg.Filter where

data FilterPrimitive : Set where
  gaussianBlur : Float → Float → FilterPrimitive
  offset       : Float → Float → FilterPrimitive
  blend        : String → String → String → FilterPrimitive  -- mode, in, in2
  colorMatrix  : String → List Float → FilterPrimitive       -- type, values
  flood        : Color → Float → FilterPrimitive             -- color, opacity
  merge        : List String → FilterPrimitive               -- input names

renderFilter : String → List FilterPrimitive → Node Model Msg
renderFilter id primitives =
  filter' (attr "id" id ∷ [])
    (map renderPrimitive primitives)

-- Drop shadow preset
dropShadow : String → Float → Float → Float → Color → Node Model Msg
dropShadow id dx dy blur color =
  renderFilter id
    ( offset dx dy
    ∷ gaussianBlur blur blur
    ∷ flood color 0.3
    ∷ blend "normal" "SourceGraphic" ""
    ∷ [])
```

### Clipping and masking

**Clip paths** (binary boundary — inside/outside):

```agda
-- Circular image crop
defs []
  ( clipPath' (attr "id" "avatar-clip" ∷ [])
      ( circle' (cxF 50.0 ∷ cyF 50.0 ∷ rF 50.0 ∷ []) ∷ [])
  ∷ [])
∷ image' ( href_ "photo.jpg" ∷ width_ "100" ∷ height_ "100"
         ∷ clipPath_ "url(#avatar-clip)" ∷ [])
∷ []

-- Animated reveal via spring-driven clip rect width
clipPath' (attr "id" "reveal" ∷ [])
  ( rect' ( x_ "0" ∷ y_ "0" ∷ height_ "100%"
          ∷ attrBind "width" (stringBinding λ m →
              showF (position (revealSpring m)) ++ "%")
          ∷ [])
  ∷ [])
```

**Masks** (luminance-based — white = visible, black = hidden, gray =
semi-transparent). Useful for soft edges and vignettes:

```agda
-- Vignette mask: radial gradient from white to black
defs []
  ( renderGradient "vignette-grad" radial
      ( mkStop 0.0 (named "white") 1.0
      ∷ mkStop 1.0 (named "black") 1.0
      ∷ [])
  ∷ mask' (attr "id" "vignette" ∷ [])
      ( rect' ( width_ "100%" ∷ height_ "100%"
              ∷ fill_ "url(#vignette-grad)" ∷ [])
      ∷ [])
  ∷ [])
-- Reference: attr "mask" "url(#vignette)"
```

### Patterns

Tiling fills for hatching, textures, backgrounds:

```agda
-- Diagonal hatch pattern
hatchPattern : String → Color → Float → Float → Node M Msg
hatchPattern id color spacing strokeW =
  pattern' ( attr "id" id ∷ attr "patternUnits" "userSpaceOnUse"
           ∷ widthF spacing ∷ heightF spacing
           ∷ attr "patternTransform" "rotate(45)" ∷ [])
    ( line' ( x1_ "0" ∷ y1_ "0" ∷ x2_ "0" ∷ y2_ (showF spacing)
            ∷ strokeC color ∷ strokeWidth_ (showF strokeW) ∷ [])
    ∷ [])

-- Usage:
defs [] ( hatchPattern "hatch" (hex "#999") 10.0 2.0 ∷ [])
∷ rect' (width_ "200" ∷ height_ "200" ∷ fill_ "url(#hatch)" ∷ [])
∷ []

-- Dot grid pattern
dotGrid : String → Color → Float → Float → Node M Msg
dotGrid id color spacing r =
  pattern' ( attr "id" id ∷ attr "patternUnits" "userSpaceOnUse"
           ∷ widthF spacing ∷ heightF spacing ∷ [])
    ( circle' ( cxF (spacing / 2.0) ∷ cyF (spacing / 2.0)
              ∷ rF r ∷ fillC color ∷ [])
    ∷ [])
```

### Markers

Arrowheads and line endings:

```agda
-- Arrow marker preset
arrowMarker : String → Color → Node M Msg
arrowMarker id color =
  marker' ( attr "id" id ∷ attr "viewBox" "0 0 10 10"
          ∷ attr "refX" "9" ∷ attr "refY" "5"
          ∷ attr "markerWidth" "6" ∷ attr "markerHeight" "6"
          ∷ attr "orient" "auto-start-reverse" ∷ [])
    ( path' (d_ "M 0 0 L 10 5 L 0 10 z" ∷ fillC color ∷ []) ∷ [])

-- Dot marker preset
dotMarker : String → Color → Float → Node M Msg
dotMarker id color r =
  marker' ( attr "id" id ∷ attr "viewBox" "-5 -5 10 10"
          ∷ attr "markerWidth" (showF (r * 2.0))
          ∷ attr "markerHeight" (showF (r * 2.0)) ∷ [])
    ( circle' (rF r ∷ fillC color ∷ []) ∷ [])

-- Usage:
defs [] ( arrowMarker "arrow" (hex "#333") ∷ [])
∷ line' ( x1_ "10" ∷ y1_ "50" ∷ x2_ "200" ∷ y2_ "50"
        ∷ stroke_ "#333" ∷ strokeWidth_ "2"
        ∷ markerEnd_ "url(#arrow)" ∷ [])
∷ []
```

## Phase 8: Path morphing (animations)

Interpolate between two paths of the same structure. Since `Path = List PathCmd`,
two paths with identical command types can be lerped point-by-point.

```agda
module Agdelte.Svg.Morph where

-- Interpolate two points
lerpPoint : Point → Point → Float → Point
lerpPoint a b t = (x a + (x b - x a) * t , y a + (y b - y a) * t)

-- Interpolate matching path commands
lerpCmd : PathCmd → PathCmd → Float → PathCmd
lerpCmd (M a)         (M b)         t = M (lerpPoint a b t)
lerpCmd (L a)         (L b)         t = L (lerpPoint a b t)
lerpCmd (C a1 a2 a3)  (C b1 b2 b3)  t = C (lerpPoint a1 b1 t) (lerpPoint a2 b2 t) (lerpPoint a3 b3 t)
lerpCmd a             _             _ = a  -- fallback: keep original if types don't match

-- Interpolate two paths (must have same number of commands)
lerpPath : Path → Path → Float → Path
lerpPath as bs t = zipWith (λ a b → lerpCmd a b t) as bs
```

### With Tween

```agda
-- Morph from circle approximation to star
morphTween : Tween Path
morphTween = record
  { elapsed = 0 ; duration = 600
  ; from = circleApprox 40.0 (50.0 , 50.0)
  ; to   = star 5 40.0 15.0 (50.0 , 50.0)
  ; easing = easeInOutFn
  ; lerp = lerpPath }

-- Bind to path
attrBind "d" (stringBinding λ m → renderPath (currentValue (morphTween m)))
```

### With dependent types (type-safe morphing)

```agda
-- Path indexed by its command structure
data PathShape : Set where
  -- encode the sequence of command types

-- Two paths with the same shape can be morphed
lerpPathSafe : ∀ {shape} → PathOf shape → PathOf shape → Float → PathOf shape
```

This guarantees at compile time that morph source and target are compatible.
A `circle` path (4 cubic beziers) can't accidentally morph into a `triangle`
(3 line segments) -- the types don't match.

### Line-drawing animation (`stroke-dasharray`)

Animate `stroke-dashoffset` from path length to 0 — the path "draws itself":

```agda
-- Path that draws itself over time
drawPath : Path → Node Model Msg
drawPath p =
  let len = pathLength p  -- from Phase 3 combinators
  in path' ( d_ (renderPath p)
           ∷ stroke_ "#4a9eff"
           ∷ fill_ "none"
           ∷ strokeDasharray_ (showF len)
           ∷ attrBind "stroke-dashoffset"
               (stringBinding λ m →
                 showF (len * (1.0 - currentValue (drawProgress m))))
           ∷ [])
```

Works with Tween (timed drawing), Spring (interactive: draw on scroll,
draw on hover), and SMIL (via `smilAttr "stroke-dashoffset"`).

`pathLength` from Phase 3 makes this fully compile-time for static paths:
no runtime measurement, no `getTotalLength()` call.

## Phase 9: SVG events (interactivity)

SVG elements support all DOM events. Agdelte's `on`/`onValue` already work:

```agda
-- Click on circle
circle' ( cxF 50.0 ∷ cyF 50.0 ∷ rF 20.0
        ∷ on "click" SelectCircle
        ∷ [])

-- Drag: mouse events on SVG element
svg ( on "mousedown" StartDrag
    ∷ on "mousemove" Drag         -- TODO: needs mouse coordinates
    ∷ on "mouseup" StopDrag
    ∷ [])
```

### Mouse position in SVG coordinates

SVG events need coordinate transformation (screen → SVG space). New event handler:

```agda
-- In Agdelte.Svg.Events
onSvgClick : (Float → Float → Msg) → Attr Model Msg
-- Runtime uses: svg.getScreenCTM().inverse() to convert clientX/clientY

onSvgDrag : (Float → Float → Msg) → (Float → Float → Msg) → Msg → Attr Model Msg
-- Start(x,y), Move(x,y), End
```

Runtime addition (~10 lines in `reactive.js`):

```javascript
// SVG coordinate conversion
function svgPoint(svg, clientX, clientY) {
  const pt = svg.createSVGPoint();
  pt.x = clientX; pt.y = clientY;
  return pt.matrixTransform(svg.getScreenCTM().inverse());
}
```

### Pointer events (touch + mouse + pen)

Mouse-only events don't work on mobile. Pointer events unify all input
devices. The coordinate conversion is the same (`getScreenCTM().inverse()`):

```agda
-- In Agdelte.Svg.Events
onSvgPointerDown : (Float → Float → Msg) → Attr Model Msg
onSvgPointerMove : (Float → Float → Msg) → Attr Model Msg
onSvgPointerUp   : Msg → Attr Model Msg

-- Drag with pointer events (works on touch + mouse)
onSvgDrag : (Float → Float → Msg)   -- move(x,y)
          → (Float → Float → Msg)   -- start(x,y)
          → Msg                     -- end
          → List (Attr Model Msg)
-- Returns multiple attrs: pointerdown, pointermove, pointerup
```

Runtime: same `svgPoint()` function, just on `pointer*` events instead
of `mouse*`. One code path for all devices.

**Pinch-zoom** (two-finger gesture) needs multi-pointer tracking:

```agda
-- Pinch zoom: distance delta between two active pointers → zoom factor
onPinch : (Float → Msg) → Attr Model Msg
-- Runtime tracks two active pointerId's, computes distance change
```

Runtime addition (~15 lines): store active pointers in a `Map<pointerId, {x,y}>`,
on `pointermove` with 2 active pointers compute distance delta.

## Phase 10: SVG + CSS integration

The CSS module and SVG module share types (`Color`, `Length`) and can work together:

### SVG in Stylesheet (CSS for SVG elements)

```agda
open import Agdelte.Css.Stylesheet

svgStyles : Stylesheet
svgStyles =
    rule "circle" ("fill" ∶ showColor (hex "#4a9eff") ∷ "transition" ∶ "r 0.2s" ∷ [])
  ∷ rule "circle:hover" ("r" ∶ "8" ∷ [])      -- CSS can animate SVG attributes!
  ∷ rule ".selected" ("stroke" ∶ showColor (named "red") ∷ "stroke-width" ∶ "3" ∷ [])
  ∷ []
```

### CSS animations on SVG elements

CSS `@keyframes` work on SVG presentation attributes:

```agda
pulseCircle : Stylesheet
pulseCircle =
    keyframeRule (mkKeyframes "pulse-r"
      ( (from , "r" ∶ "20" ∷ [])
      ∷ (at 50, "r" ∶ "25" ∷ [])
      ∷ (to  , "r" ∶ "20" ∷ [])
      ∷ []))
  ∷ rule ".pulse" (animation' (record (anim "pulse-r" (s 1.0))
      { count = infinite }) ∷ [])
  ∷ []
```

## Phase 11: Static SVG file generation

Same pattern as CSS: `renderStylesheet` produces `.css`, `renderSvg` produces `.svg`.

```agda
module Agdelte.Svg.Render where

renderSvg : ViewBox → List (Node ⊤ ⊥) → String
-- Renders an SVG tree to an XML string (no model, no events)
```

Use cases: icons, logos, illustrations generated from mathematical definitions
at build time. A `generate-svg.js` script (like `generate-css.js`):

```bash
node scripts/generate-svg.js jAgda.Icons starIcon icons/star.svg
```

The generated `.svg` file is static, cacheable, usable as `<img src="star.svg">`.
The same `Path`/`Transform`/`Gradient` types work for both runtime reactive SVG
and build-time static SVG.

### Testing SVG output

Three levels of testing:

**1. Compile-time path verification** — already possible with `refl`:

```agda
_ : renderPath triangle ≡ "M0 100 L50 0 L100 100 Z"
_ = refl

_ : pathLength (M (0.0 , 0.0) ∷ L (100.0 , 0.0) ∷ []) ≡ 100.0
_ = refl
```

**2. Static SVG snapshot testing** — `renderSvg` produces a string,
compare against reference:

```bash
node scripts/generate-svg.js jAgda.Tests.SvgOutput testIcon /tmp/test.svg
diff /tmp/test.svg test/fixtures/expected-icon.svg
```

**3. Visual regression** — outside Agda's scope. Use Playwright screenshots
on the rendered HTML+SVG pages.

## Phase 12: Accessibility

SVG accessibility requires `<title>`, `<desc>`, `role`, and `aria-*` attributes.

```agda
-- Accessible SVG: title + desc for screen readers
accessibleSvg : String → String → List (Attr M Msg) → List (Node M Msg) → Node M Msg
accessibleSvg title desc attrs children =
  svg (attr "role" "img" ∷ attr "aria-labelledby" "title desc" ∷ attrs)
    ( elem "title" [] (text title ∷ [])
    ∷ elem "desc" [] (text desc ∷ [])
    ∷ children)

-- Decorative SVG: hidden from screen readers
decorativeSvg : List (Attr M Msg) → List (Node M Msg) → Node M Msg
decorativeSvg attrs = svg (attr "aria-hidden" "true" ∷ attr "focusable" "false" ∷ attrs)
```

## Phase 13: SMIL animations (declarative)

SVG has built-in animation elements that run without JavaScript. SMIL's
unique strength is **declarative choreography**: sequence, sync, and trigger
animations entirely in markup.

### Animation elements

SVG defines four animation elements:

| Element | Purpose |
|---------|---------|
| `<animate>` | Animate a single attribute over time |
| `<animateTransform>` | Animate `transform` (rotate, scale, translate, skew) |
| `<animateMotion>` | Move element along a path |
| `<set>` | Set attribute to value at a time (discrete, no interpolation) |

### Core data type

```agda
module Agdelte.Svg.Smil where

-- Timing: when animation starts and ends
data Timing : Set where
  offset     : Duration → Timing                  -- begin="2s"
  onEvent    : String → Timing                    -- begin="click", "mouseover", "focusin", ...
  syncBegin  : String → Timing                    -- begin="anim1.begin"
  syncBeginD : String → Duration → Timing         -- begin="anim1.begin + 0.3s"
  syncEnd    : String → Timing                    -- begin="anim1.end"
  syncEndD   : String → Duration → Timing         -- begin="anim1.end + 0.5s"
  syncRepeat : String → ℕ → Timing               -- begin="anim1.repeat(2)"
  anyOf      : List Timing → Timing               -- begin="2s; click" (first wins)

-- Interpolation mode
data CalcMode : Set where
  discrete linear paced spline : CalcMode

-- How animation composes with base value
data Additive : Set where
  replace sum : Additive

-- Restart behavior
data Restart : Set where
  always whenNotActive never : Restart

-- Repeat behavior
data RepeatCount : Set where
  once        : RepeatCount
  times       : ℕ → RepeatCount
  indefinite  : RepeatCount

-- Fill behavior (what happens after animation ends)
data FillMode : Set where
  remove freeze : FillMode

-- Transform type for animateTransform
data TransformType : Set where
  translateT rotateT scaleT skewXT skewYT : TransformType

-- The core animation record
record SmilAnim : Set where
  field
    dur        : Duration
    begin      : Timing           -- default: offset 0
    repeatCount : RepeatCount     -- default: once
    fill       : FillMode         -- default: remove
    additive   : Additive         -- default: replace
    calcMode   : CalcMode         -- default: linear
    restart    : Restart          -- default: always
    id         : Maybe String     -- for sync references

-- Concrete animation types
data SmilNode (M Msg : Set) : Set where
  -- Animate a single attribute: from → to
  animate       : String → String → String → SmilAnim → SmilNode M Msg
  -- Animate with keyframe values
  animateValues : String → List String → SmilAnim → SmilNode M Msg
  -- Animate transform
  animateTransform : TransformType → String → String → SmilAnim → SmilNode M Msg
  -- Move along path
  animateMotion : Path → MotionOpts → SmilAnim → SmilNode M Msg
  -- Discrete set (no interpolation)
  set'          : String → String → SmilAnim → SmilNode M Msg

record MotionOpts : Set where
  field
    autoRotate : Bool        -- rotate="auto" (orient along path)
    keyPoints  : List Float  -- timing along path (0.0 to 1.0)
```

### Rendering

```agda
renderSmil : SmilNode M Msg → Node M Msg
renderSmil (animate attrName from to opts) =
  elem "animate"
    ( attr "attributeName" attrName
    ∷ attr "from" from ∷ attr "to" to
    ∷ renderOpts opts) []

renderSmil (animateValues attrName vals opts) =
  elem "animate"
    ( attr "attributeName" attrName
    ∷ attr "values" (intercalate ";" vals)
    ∷ renderOpts opts) []

renderSmil (animateTransform typ from to opts) =
  elem "animateTransform"
    ( attr "attributeName" "transform"
    ∷ attr "type" (showTransformType typ)
    ∷ attr "from" from ∷ attr "to" to
    ∷ renderOpts opts) []

renderSmil (animateMotion path motionOpts opts) =
  elem "animateMotion"
    ( attr "path" (renderPath path)
    ∷ (if autoRotate motionOpts then attr "rotate" "auto" ∷ [] else [])
    ∷ renderOpts opts) []

renderSmil (set' attrName value opts) =
  elem "set"
    ( attr "attributeName" attrName
    ∷ attr "to" value
    ∷ renderOpts opts) []

-- Shared options rendering
renderOpts : SmilAnim → List (Attr M Msg)
renderOpts opts =
    attr "dur" (showDuration (dur opts))
  ∷ renderTiming (begin opts)
  ∷ renderRepeat (repeatCount opts)
  ∷ renderFill (fill opts)
  ∷ renderAdditive (additive opts)
  ∷ renderCalcMode (calcMode opts)
  ∷ maybe [] (λ i → attr "id" i ∷ []) (id opts)

renderTiming : Timing → Attr M Msg
renderTiming (offset d)         = attr "begin" (showDuration d)
renderTiming (onEvent ev)       = attr "begin" ev
renderTiming (syncBegin id)     = attr "begin" (id ++ ".begin")
renderTiming (syncBeginD id d)  = attr "begin" (id ++ ".begin + " ++ showDuration d)
renderTiming (syncEnd id)       = attr "begin" (id ++ ".end")
renderTiming (syncEndD id d)    = attr "begin" (id ++ ".end + " ++ showDuration d)
renderTiming (syncRepeat id n)  = attr "begin" (id ++ ".repeat(" ++ show n ++ ")")
renderTiming (anyOf ts)         = attr "begin" (intercalate "; " (map showTiming ts))
```

### Keyframes with easing

`values` + `keyTimes` + `keySplines` = SMIL's equivalent of CSS `@keyframes`:

```agda
-- Bounce effect: radius 10 → 15 → 10, with ease-in-out between steps
circle' (cxF 50.0 ∷ cyF 50.0 ∷ rF 10.0 ∷ [])
  ( renderSmil (animateValues "r"
      ("10" ∷ "15" ∷ "12" ∷ "10" ∷ [])
      record defaultSmil
        { dur = ms 600
        ; repeatCount = indefinite
        ; calcMode = spline })
  ∷ [])
```

When `calcMode = spline`, `keySplines` controls easing between each pair
of values (cubic bezier, same format as CSS `cubic-bezier()`):

```agda
-- keySplines: one curve per segment (n values → n-1 splines)
data KeySpline : Set where
  mkSpline : Float → Float → Float → Float → KeySpline

-- Reuse CSS easing definitions
easeOut   = mkSpline 0.0 0.0 0.58 1.0
easeInOut = mkSpline 0.42 0.0 0.58 1.0
```

### Choreography (sequencing)

SMIL's most distinctive feature: animations reference each other by `id`
for declarative sequencing. No JavaScript, no timers:

```agda
-- Three-step animation sequence: fade in → pulse → settle

-- Step 1: fade in over 0.5s
fadeIn : SmilNode M Msg
fadeIn = animate "opacity" "0" "1"
  record defaultSmil
    { dur = ms 500 ; fill = freeze
    ; id = just "fadeIn" }

-- Step 2: pulse radius, starts when fadeIn ends
pulse : SmilNode M Msg
pulse = animateValues "r"
  ("20" ∷ "25" ∷ "20" ∷ [])
  record defaultSmil
    { dur = ms 400
    ; begin = syncEnd "fadeIn"
    ; id = just "pulse" }

-- Step 3: color shift, starts 0.2s after pulse ends
colorShift : SmilNode M Msg
colorShift = animate "fill" "#4a9eff" "#ff6b6b"
  record defaultSmil
    { dur = ms 300 ; fill = freeze
    ; begin = syncEndD "pulse" (ms 200) }

-- All three on one element:
circle' (cxF 50.0 ∷ cyF 50.0 ∷ rF 20.0 ∷ opacity_ "0" ∷ [])
  ( renderSmil fadeIn
  ∷ renderSmil pulse
  ∷ renderSmil colorShift
  ∷ [])
```

This compiles to:
```xml
<circle cx="50" cy="50" r="20" opacity="0">
  <animate id="fadeIn" attributeName="opacity" from="0" to="1"
           dur="0.5s" fill="freeze"/>
  <animate id="pulse" attributeName="r" values="20;25;20"
           dur="0.4s" begin="fadeIn.end"/>
  <animate id="colorShift" attributeName="fill" from="#4a9eff" to="#ff6b6b"
           dur="0.3s" fill="freeze" begin="pulse.end+0.2s"/>
</circle>
```

No JS executed. Browser handles timing, interpolation, and GPU compositing.

### Interactive trigger

SMIL animations can start on user interaction:

```agda
-- Click to expand
circle' (cxF 50.0 ∷ cyF 50.0 ∷ rF 10.0 ∷ [])
  ( renderSmil (animate "r" "10" "30"
      record defaultSmil
        { dur = ms 200 ; fill = freeze
        ; begin = onEvent "click" })
  ∷ [])

-- Auto-start after 1s OR on mouseover (whichever comes first)
renderSmil (animate "opacity" "0" "1"
    record defaultSmil
      { dur = ms 300 ; fill = freeze
      ; begin = anyOf (offset (s 1) ∷ onEvent "mouseover" ∷ [])
      ; restart = never })  -- don't re-trigger once played
```

### animateTransform

Animate rotation, scale, translation, skew:

```agda
-- Continuous rotation
g (transform_ "translate(100,100)" ∷ [])
  ( rect' (x_ "-20" ∷ y_ "-20" ∷ width_ "40" ∷ height_ "40" ∷ [])
  ∷ renderSmil (animateTransform rotateT "0" "360"
      record defaultSmil
        { dur = s 3 ; repeatCount = indefinite })
  ∷ [])

-- Scale bounce on hover
renderSmil (animateTransform scaleT "1" "1.2"
    record defaultSmil
      { dur = ms 200 ; fill = freeze
      ; begin = onClick })
```

### animateMotion

Move element along a typed `Path`:

```agda
-- Satellite orbiting along elliptical path
circle' (rF 5.0 ∷ fillC (hex "#ff6b6b") ∷ [])
  ( renderSmil (animateMotion
      (circleApprox 80.0 (0.0 , 0.0))  -- path from Phase 3
      record { autoRotate = true ; keyPoints = [] }
      record defaultSmil
        { dur = s 4 ; repeatCount = indefinite })
  ∷ [])
```

`autoRotate = true` orients the element tangent to the path — critical
for vehicles, arrows, particles following curves.

### Additive and accumulate

`additive = sum`: animation value is **added** to the base value, not
replacing it. Enables layered animations on the same attribute:

```agda
-- Base position + wobble overlay
circle' (cxF 100.0 ∷ cyF 100.0 ∷ rF 10.0 ∷ [])
  ( renderSmil (animate "cx" "0" "20"
      record defaultSmil
        { dur = ms 200 ; repeatCount = indefinite
        ; additive = sum })  -- adds 0→20 to base cx=100
  ∷ [])
```

### SMIL vs model-driven vs CSS

| | SMIL | CSS animation | Spring/Tween |
|---|------|--------------|--------------|
| Runs in | Browser (GPU) | Browser (GPU) | JS (per frame) |
| Sequencing | Declarative (`begin="id.end"`) | Manual (`animation-delay`) | Manual (model logic) |
| Trigger | `begin="click"` | `:hover`, class toggle | Event → Msg |
| Attribute scope | Any SVG attribute | CSS properties only | Any model field |
| Multi-step | `values` + `keyTimes` | `@keyframes` | Multiple tweens |
| Path motion | `<animateMotion>` | `offset-path` (limited) | Manual coordinate calc |
| Best for | SVG decorations, sequences | CSS properties, hover | App logic, data-driven |

**Boundary rule:** if the intermediate value never enters `update` (pure
decoration), use SMIL or CSS. If it does (collision, threshold, conditional
logic), use Spring/Tween in the model.

### Default record

```agda
defaultSmil : SmilAnim
defaultSmil = record
  { dur = s 1
  ; begin = offset (ms 0)
  ; repeatCount = once
  ; fill = remove
  ; additive = replace
  ; calcMode = linear
  ; restart = always
  ; id = nothing }
```

## Performance considerations

### Large SVGs (1000+ elements)

`foreach` with 1000 data points creates 1000 `<circle>` elements, each
with reactive bindings. This works but has cost:
- Initial render: 1000 `createElementNS` calls
- Each update: 1000 binding checks (even if most didn't change)

Mitigations:
- `scope`/`scopeProj` on SVG subtrees to skip unchanged regions
- `foreachKeyed` for efficient add/remove (no full rebuild)
- For truly static SVG, use Phase 11 (`.svg` file generation)
- For 10K+ points, consider Canvas (not SVG)

### Binding granularity

One `attrBind` per attribute means fine-grained updates. For a scatter plot
with 1000 points where only `cx`/`cy` change, the runtime checks 2000 bindings.
If the data changes rarely, this is efficient. If it changes every frame
(real-time streaming), consider a coarser approach: a single `attrBind "d"`
on a `<path>` element that renders all points as one path string.

### scope for SVG subtrees

```agda
-- Skip updating the legend when only data changes
scope (λ m → show (length (getData m)))
  (g [] (foreach getData renderDataPoint ∷ []))
```

## What dependent types bring to SVG

### 1. Path structure verification

CSS had string escape hatches with no validation. SVG paths get **typed
command sequences**. A `PathCmd` is a sum type -- can't write `"X 10 20"`
because `X` doesn't exist as a constructor.

### 2. Compile-time geometry

Mathematical curves (spirals, fractals, parametric surfaces) computed at
compile time. The browser receives pre-computed `d="M0 0 L1.2 3.4 ..."`,
not code that runs.

### 3. Safe morphing

Two paths with different structures can't be morphed -- type error.
No runtime "invalid path interpolation" bugs.

### 4. Gradient stop ordering

```agda
-- Dependent type: stops must be in ascending offset order
data OrderedStops : Float → Set where
  end  : OrderedStops 1.0
  cons : ∀ {prev} → (s : GradientStop) → offset s > prev → OrderedStops (offset s) → OrderedStops prev
```

### 5. ViewBox invariants

```agda
-- Width and height must be positive
ValidViewBox : ViewBox → Set
ValidViewBox vb = (width vb > 0.0) × (height vb > 0.0)
```

### 6. Reactive data visualization with O(bindings) updates

SVG + `bindF`/`attrBind` = live charts that update individual attributes,
not rebuild the entire SVG tree. 1000 data points with `foreach` means
1000 `<circle>` elements, each with its own reactive bindings. Change one
data point → one `cx`/`cy` update. O(1) per changed datum.

## File structure

```
src/Agdelte/Svg/
  Elements.agda       -- svg, g, circle', rect', path', defs, clipPath', mask', pattern', marker', foreignObject', etc.
  Attributes.agda     -- x_, y_, cx_, cy_, fill_, stroke_, viewBox_, textAnchor_, dominantBaseline_, etc.
  Text.agda           -- multilineText, textOnPath helpers
  Path.agda           -- PathCmd, Path, renderPath, pathLength, path combinators
  Path/
    Generators.agda   -- regularPolygon, star, sineWave, spiral, roundRect, circleApprox
    Morph.agda        -- lerpPath, lerpCmd, drawPath (line-drawing animation)
  Transform.agda      -- Transform, renderTransforms
  ViewBox.agda        -- ViewBox, zoomViewBox, panViewBox, preserveAspectRatio
  Gradient.agda       -- GradientStop, GradientDir, renderGradient
  Filter.agda         -- FilterPrimitive, renderFilter, dropShadow
  Clip.agda           -- clip path helpers, mask helpers (vignette, animated reveal)
  Pattern.agda        -- hatchPattern, dotGrid
  Marker.agda         -- arrowMarker, dotMarker
  Events.agda         -- onSvgClick, onSvgDrag, onSvgPointerDown/Move/Up, onPinch
  Render.agda         -- renderSvg (static .svg file generation)
  Accessibility.agda  -- accessibleSvg, decorativeSvg
  Smil.agda           -- Timing, SmilAnim, SmilNode, renderSmil, defaultSmil, choreography helpers

src/Agdelte/Svg.agda  -- re-exports all above

scripts/generate-svg.js  -- extract SVG strings from compiled JS to .svg files
```

## Implementation order

1. **Phase 0** -- Runtime namespace fix (`reactive.js`, `dom.js`). ~22 lines.
   Unblocks everything else.
2. **Phase 1** -- Element constructors. ~60 lines of trivial wrappers.
3. **Phase 2** -- Attribute helpers + text helpers. ~120 lines.
   Includes text attributes, `multilineText`, `textOnPath`.
4. **Phase 3** -- Typed path DSL + `pathLength`. High value. ~170 lines.
5. **Phase 4** -- Typed transforms. ~40 lines.
6. **Phase 9** -- SVG events + pointer events. ~40 lines runtime.
   Mouse, touch, pen unified via pointer events. `onPinch` for zoom.
7. **Phase 6** -- Data visualization + `foreignObject`. Examples, not library code.
   Includes `foreignObject` tooltip pattern.
8. **Phase 5** -- ViewBox helpers. ~30 lines.
9. **Phase 7** -- Gradients, filters, clips, masks, patterns, markers. ~180 lines.
10. **Phase 8** -- Path morphing + line-drawing animation. ~70 lines.
    Depends on Phase 3 (`pathLength` for stroke-dasharray).
11. **Phase 10** -- CSS integration (shared Color, Stylesheet for SVG).
12. **Phase 11** -- Static `.svg` file generation + testing. ~60 lines + build script.
    Three test levels: compile-time `refl`, snapshot diff, visual regression.
13. **Phase 12** -- Accessibility helpers. ~20 lines.
14. **Phase 13** -- SMIL animations. ~200 lines (types + rendering + presets).
    High value for SVG-heavy applications (zero-JS choreographed sequences).

## Relation to other modules

### Css module

Shares `Color`, `Length`. SVG presentation attributes (`fill`, `stroke`)
accept the same `Color` type. CSS `@keyframes` can animate SVG attributes.
`Stylesheet` rules can target SVG elements by class.

### Anim module

`Spring`/`Tween` drive SVG attributes via `attrBind`. Interactive pan/zoom
on viewBox, smooth path morphing, spring-driven transforms. No new
animation primitives needed -- existing `tickSpring`/`tickTween` work
directly with SVG floats.

### Agent module

An interactive SVG visualization is an Agent: position/zoom/selection is
state, mouse events are input, rendered SVG is output. Composable with
other agents via standard wiring (`>>>`, `***`). A chart component
zoomed via `zoomNode` into a dashboard layout.

### Theory

SVG path as coalgebra: a parametric curve `[0,1] → Point` is a coalgebra
of `p(y) = Point × y^Float`. Path generators (spiral, sine) are
coalgebras sampled at discrete points. Morph is a natural transformation
between two path coalgebras. The polynomial functor framework unifies
path generation, animation, and event handling under one abstraction.

## Known limitations

### Nesting validation

`Node` is untyped regarding nesting — nothing prevents putting `<div>`
inside `<circle>` or `<rect>` inside `<linearGradient>`. Full validation
via indexed types (Node carries its tag, children constrained by parent)
would be very complex and not worth the ergonomic cost. The browser silently
ignores invalid children. Smart constructors provide soft protection:
`circle'` with `[]` children by convention makes accidental nesting unlikely.

### Text measurement

SVG text metrics (`getComputedTextLength()`, `getSubStringLength()`) require
the DOM. Auto-sizing text boxes or justified text can't be computed in Agda.
Would need a new `Cmd` variant: `measureText : String → (Float → Msg) → Cmd Msg`.

## Open questions

### Relative path commands: naming conflicts

Lowercase constructors `m`, `l`, `c`, `s`, `t`, `a` conflict with common
Agda variable names. Options:

1. **Suffix convention:** `mRel`, `lRel`, `cRel`, `sRel`, `tRel`, `aRel`
2. **Module-qualified:** `PathCmd.m`, `PathCmd.l` — verbose but unambiguous
3. **Separate type:** `data RelPathCmd` — cleaner but duplicates structure
4. **Skip relative commands initially** — most SVG uses absolute coordinates

**Recommendation: option 1 (suffix convention).** Path DSL code tends to be
dense — long chains of commands that should read fluently:

```agda
M (10.0 , 20.0) ∷ lRel (5.0 , 0.0) ∷ vRel 10.0 ∷ Z ∷ []
```

Module-qualified `PathCmd.l` is too noisy for this use case. A separate
`RelPathCmd` type would force `showCmd` to handle two types and complicate
`lerpCmd` (which needs to match absolute against relative). The suffix
convention is ugly but practical: `mRel`, `lRel`, `hRel`, `vRel`, `cRel`,
`sRel`, `qRel`, `tRel`, `aRel`. Nine constructors — not a large surface.

That said, option 4 is a fine starting point. Programmatically generated
SVG paths (the main use case for this framework) almost always use absolute
coordinates — relative commands are a convenience for hand-written SVG.
Add relative commands later when someone actually needs them.

### Shape elements and SMIL children

Phase 1 defines `circle'`, `rect'` etc. as leaf nodes (no children). Phase 13
needs children for `<animate>` elements. Options:

1. **Two variants:** `circle'` (leaf) and `circleAnim` (with children)
2. **Always accept children:** `circle' attrs children` — simpler but less
   precise (most circles have no children)
3. **SMIL as attributes:** encode `<animate>` as special `Attr` values so
   shape elements stay childless

**Recommendation: option 2 (always accept children).** The existing HTML
constructors already follow this pattern — `div`, `span`, `button` all take
children even when they're often empty. Writing `circle' attrs []` is
natural Agda and matches the rest of the API. Having two names per element
(`circle'` / `circleAnim`) doubles the API surface for a marginal benefit.
Option 3 (SMIL as Attr) is tempting for type purity but misrepresents the
DOM structure — `<animate>` is a child element, not an attribute. Encoding
it as `Attr` would require special-casing in the runtime renderer.

Concretely: redefine all Phase 1 shape constructors to take children:

```agda
circle' : ∀ {M Msg} → List (Attr M Msg) → List (Node M Msg) → Node M Msg
circle' = elem "circle"
```

Code that doesn't use SMIL simply passes `[]`. Code that does passes
`renderSmil ... ∷ []`.

### ID management for `<use>` / `<defs>`

SVG's `<use href="#id">` pattern requires unique IDs. Currently IDs are
bare strings with no uniqueness guarantee. Options:

1. **String IDs** (current) — simple, user manages uniqueness
2. **Typed IDs:** `data SvgId = mkId String` with `defineId`/`refId` pairs
3. **Scoped IDs:** component-local IDs prefixed automatically (like CSS modules)

**Recommendation: option 1 (string IDs) now, option 2 later if needed.**
The `<defs>` / `<use>` pattern is explicit by nature — the programmer defines
an ID in one place and references it in another. String IDs are simple,
match the SVG spec directly, and the programmer already manages ID uniqueness
when writing SVG in any other tool. Adding `SvgId` wrapping now would be
abstraction without a concrete problem to solve.

If collisions become an issue in practice (e.g. composing two independently
authored SVG components into one page), then add typed IDs. The migration
is mechanical: wrap strings in a newtype, replace `attr "id"` with `defineId`,
replace `fill_ "url(#...)"` with `refId`. But don't build this until
there's a real collision.

### Path as standalone module?

`Path` (points, curves, transforms) is useful beyond SVG: Canvas drawing,
game geometry, geographic data. Should it live at `Agdelte.Svg.Path` or
at a more general location like `Agdelte.Geometry.Path`?

Current plan keeps it under `Svg/` for simplicity. Can be refactored later
if reuse demand appears.

**Recommendation: keep under `Svg/`.** The path DSL is designed around SVG's
path command language (`M`, `L`, `C`, `A`, `Z`) — it renders to SVG path
strings. A hypothetical Canvas backend would need different output (Canvas
API calls, not `d` strings), so the rendering half wouldn't be shared anyway.
The `Point` type and geometric generators (star, spiral) could potentially
be reused, but extracting them now would be premature. If Canvas support is
ever added, the refactoring is trivial: move `Point` and generators to
`Agdelte.Geometry`, re-export from `Agdelte.Svg.Path` for backward
compatibility. One rename, zero breakage.

### SMIL animation IDs and choreography safety

SMIL sequencing (`begin="fadeIn.end"`) depends on string IDs. A typo in
`"fadIn.end"` doesn't error — the animation simply never starts. This is
worse than the `<use href="#id">` problem because:
- `<use>` with wrong ID: element missing → visually obvious
- SMIL with wrong ID: animation waits forever → subtle silent bug

Options:

1. **String IDs** — same as `<defs>`/`<use>`, user manages correctness
2. **Typed `SmilId`** — newtype with `define`/`syncTo` pairs that guarantee
   matching. But choreography often spans multiple elements, so the ID must
   be visible across the component.
3. **Name-based constructors** — `SmilAnim` stores the ID, `syncEnd` takes
   the `SmilAnim` value directly instead of a string:

```agda
-- Instead of:
fadeIn = ... { id = just "fadeIn" }
pulse  = ... { begin = syncEnd "fadeIn" }

-- Could be:
fadeIn = ... { id = just "fadeIn" }
pulse  = ... { begin = after fadeIn }
-- where `after : SmilAnim → Timing` extracts the id field
```

**Recommendation:** option 3 is the most Agda-idiomatic. `after` is a
one-line function that extracts the ID from the `SmilAnim` record. If
`id = nothing`, it's a compile-time error (incomplete pattern match or
`Maybe` handling). This catches typos without any newtype ceremony.

Limitation: `after` only works when both animations are defined in the same
Agda module (the value must be in scope). For cross-component choreography
(animations in separate `zoomNode` subtrees), string IDs remain the only
option — but this is rare and the programmer is already managing component
boundaries explicitly.

### SMIL vs reactive model conflict

If a SMIL `<animate>` runs on an attribute that `attrBind` also controls,
the behavior is:
- SMIL animation **overrides** the attribute during playback
  (SMIL values have higher priority than DOM attributes)
- When SMIL ends (with `fill = remove`), the `attrBind` value reappears
- With `fill = freeze`, SMIL's final value sticks and `attrBind` is
  effectively dead

This is a real conflict.

#### Approach 1: SMIL as `Attr` variant (structural guarantee)

Currently SMIL is a child `Node` and attributes are `Attr` — two separate
lists. The conflict is invisible. But if SMIL animations are declared as
`Attr` values alongside `attr`/`attrBind`, the conflict is in one place:

```agda
-- New Attr constructor:
data Attr (Model Msg : Set) : Set₁ where
  attr      : String → String → Attr Model Msg
  attrBind  : String → Binding Model String → Attr Model Msg
  on        : String → Msg → Attr Model Msg
  onValue   : String → (String → Msg) → Attr Model Msg
  style     : String → String → Attr Model Msg
  styleBind : String → Binding Model String → Attr Model Msg
  -- NEW: SMIL animation targeting an attribute
  smilAttr  : String → SmilNode → Attr Model Msg
```

Usage:

```agda
-- r is SMIL-animated: declared in attrs, not in children
circle' ( cxF 50.0 ∷ cyF 50.0
        ∷ smilAttr "r" (animateValues ("10" ∷ "15" ∷ "10" ∷ [])
            record defaultSmil { dur = s 1 ; repeatCount = indefinite })
        ∷ fillC (hex "#4a9eff")
        ∷ []) []
```

The renderer sees `smilAttr "r" ...` in the attr list and emits an
`<animate attributeName="r" ...>` child element. From the Agda side,
the attribute source is declared once. If someone writes both
`attrBind "r" ...` and `smilAttr "r" ...` in the same list, it's
visible in one place — and a `checkAttrs` function can catch it:

```agda
-- Pure, runs at compile time (or unit test)
checkAttrs : List (Attr M Msg) → Maybe String
checkAttrs attrs =
  let names = concatMap attrNames attrs  -- extract all attribute names
      dups  = findDuplicates names
  in if null dups then nothing
     else just ("Duplicate attribute: " ++ head dups)

-- Compile-time assertion:
_ : checkAttrs myCircleAttrs ≡ nothing
_ = refl
```

This doesn't require indexed types or tracked attribute sets — it's a
plain function that Agda evaluates at compile time via `refl`. If there's
a duplicate, `refl` fails to typecheck.

#### Recommendation

**Approach 1 (`smilAttr` as `Attr` variant + `checkAttrs`).** It fits
the existing API (`List (Attr M Msg)` stays open and uniform across all
elements), provides a compile-time check without new types, and the
`checkAttrs` pattern is reusable for other invariants.

The key insight: moving SMIL from children to attrs is not just about
conflict detection — it's the right abstraction. SMIL `<animate>` targets
a specific attribute by name. It *is* an attribute declaration, not a
child element. The DOM representation (child element) is an implementation
detail that the Agda DSL can abstract away.

### `Timing` event string safety

`onEvent : String → Timing` accepts any string: `"click"`, `"mouseover"`,
but also `"typo"`. SVG only supports a fixed set of event names for SMIL
`begin`/`end`:

`click`, `mousedown`, `mouseup`, `mouseover`, `mouseout`, `mousemove`,
`focusin`, `focusout`, `activate`, `beginEvent`, `endEvent`, `repeatEvent`

Options:

1. **String** — flexible, typos silent
2. **`data SmilEvent`** — safe, but closed (can't extend)
3. **Smart constructors** — `onClick = onEvent "click"`, etc., with raw
   `onEvent` available as escape hatch

```agda
-- Typed events as smart constructors (no new type needed)
onClick onMouseover onMouseout onFocusin onFocusout : Timing
onClick     = onEvent "click"
onMouseover = onEvent "mouseover"
onMouseout  = onEvent "mouseout"
onFocusin   = onEvent "focusin"
onFocusout  = onEvent "focusout"
```

**Recommendation: option 3 (smart constructors).** Same pattern as HTML
elements (`div = elem "div"`). The typed names cover 99% of usage. Raw
`onEvent` remains available for edge cases. No new type, no pattern
matching changes, no closed-world assumption. The user writes `onClick`
not `onEvent "click"` — typos eliminated for the common case.
