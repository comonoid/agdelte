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

## Phase 0: Runtime namespace fix

The only blocking change. Two files, ~15 lines total.

### Tag-based namespace detection

```javascript
const SVG_NS = 'http://www.w3.org/2000/svg';

const SVG_TAGS = new Set([
  'svg', 'g', 'defs', 'symbol', 'use',
  'circle', 'ellipse', 'line', 'path', 'polygon', 'polyline', 'rect',
  'text', 'tspan', 'textPath',
  'image', 'foreignObject',
  'clipPath', 'mask', 'marker', 'pattern',
  'linearGradient', 'radialGradient', 'stop',
  'filter', 'feBlend', 'feColorMatrix', 'feComponentTransfer',
  'feComposite', 'feConvolveMatrix', 'feDiffuseLighting',
  'feDisplacementMap', 'feFlood', 'feGaussianBlur', 'feImage',
  'feMerge', 'feMergeNode', 'feMorphology', 'feOffset',
  'feSpecularLighting', 'feTile', 'feTurbulence',
  'feFuncR', 'feFuncG', 'feFuncB', 'feFuncA',
  'fePointLight', 'feSpotLight', 'feDistantLight',
  'animate', 'animateMotion', 'animateTransform', 'set',
]);
```

### Element creation (reactive.js + dom.js)

```javascript
// Before:
const el = document.createElement(tag);

// After:
const el = SVG_TAGS.has(tag)
  ? document.createElementNS(SVG_NS, tag)
  : document.createElement(tag);
```

### Namespaced attributes

SVG uses `xlink:href` and `xml:lang`. These need `setAttributeNS`:

```javascript
const XLINK_NS = 'http://www.w3.org/1999/xlink';

function setAttr(el, name, value) {
  if (name === 'xlink:href' || name === 'href' && SVG_TAGS.has(el.tagName.toLowerCase())) {
    el.setAttributeNS(XLINK_NS, 'href', value);
  } else {
    el.setAttribute(name, value);
  }
}
```

After Phase 0, bare `elem "circle"` renders correctly. Everything below builds
on top of this foundation.

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

## Phase 7: SVG gradients and filters (typed DSL)

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
  Elements.agda       -- svg, g, circle', rect', path', etc.
  Attributes.agda     -- x_, y_, cx_, cy_, fill_, stroke_, viewBox_, etc.
  Path.agda           -- PathCmd, Path, renderPath, path combinators
  Path/
    Generators.agda   -- regularPolygon, star, sineWave, spiral, roundRect
    Morph.agda        -- lerpPath, lerpCmd
  Transform.agda      -- Transform, renderTransforms
  ViewBox.agda        -- ViewBox, zoomViewBox, panViewBox
  Gradient.agda       -- GradientStop, GradientDir, renderGradient
  Filter.agda         -- FilterPrimitive, renderFilter, dropShadow
  Events.agda         -- onSvgClick, onSvgDrag (SVG coordinate conversion)

src/Agdelte/Svg.agda  -- re-exports all above
```

## Implementation order

1. **Phase 0** -- Runtime namespace fix (`reactive.js`, `dom.js`). ~15 lines.
   Unblocks everything else.
2. **Phase 1** -- Element constructors. ~60 lines of trivial wrappers.
3. **Phase 2** -- Attribute helpers. ~80 lines. Enables idiomatic SVG.
4. **Phase 3** -- Typed path DSL. High value. ~150 lines.
5. **Phase 4** -- Typed transforms. ~40 lines.
6. **Phase 9** -- SVG events (coordinate conversion). ~20 lines runtime.
7. **Phase 6** -- Data visualization patterns (foreach + attrBind).
   Examples, not library code.
8. **Phase 5** -- ViewBox helpers. ~30 lines.
9. **Phase 7** -- Gradients, filters. ~100 lines.
10. **Phase 8** -- Path morphing. ~50 lines. Depends on Phase 3.
11. **Phase 10** -- CSS integration (shared Color, Stylesheet for SVG).

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
