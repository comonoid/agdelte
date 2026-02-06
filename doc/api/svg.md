# SVG (Typed SVG DSL)

From `Agdelte.Svg` (re-exports all submodules).

## Overview

The SVG module provides a complete typed DSL for creating SVG graphics with:
- Namespace-aware rendering (automatic `createElementNS`)
- 40+ element constructors
- 80+ typed attribute helpers
- Typed path commands with compile-time validation
- Transform composition
- SMIL declarative animations
- SVG-specific event handlers with coordinate conversion
- Accessibility helpers

## Elements

From `Agdelte.Svg.Elements`.

All elements take `List (Attr M Msg)` and `List (Node M Msg)` to support SMIL animation children.

### Container Elements

| Function | Description |
|----------|-------------|
| `svg` | Root SVG element |
| `g` | Group element |
| `defs` | Definitions container |
| `symbol'` | Reusable symbol |
| `marker'` | Line marker |
| `clipPath'` | Clipping path |
| `mask'` | Mask |
| `pattern'` | Repeating pattern |
| `a'` | Link element |
| `switch'` | Conditional rendering |

### Shape Elements

| Function | Description |
|----------|-------------|
| `circle'` | Circle |
| `rect'` | Rectangle |
| `ellipse'` | Ellipse |
| `line'` | Line |
| `polyline'` | Open polyline |
| `polygon'` | Closed polygon |
| `path'` | Path element |

### Text Elements

| Function | Description |
|----------|-------------|
| `svgText` | Text element |
| `tspan'` | Text span |
| `textPath'` | Text on path |

### Gradient Elements

| Function | Description |
|----------|-------------|
| `linearGradient'` | Linear gradient |
| `radialGradient'` | Radial gradient |
| `stop'` | Gradient stop |

### Filter Elements

| Function | Description |
|----------|-------------|
| `filter'` | Filter container |
| `feGaussianBlur'` | Gaussian blur |
| `feOffset'` | Offset |
| `feBlend'` | Blend |
| `feColorMatrix'` | Color matrix |
| `feMerge'` | Merge |
| `feMergeNode'` | Merge node |
| `feFlood'` | Flood fill |
| `feComposite'` | Composite |
| `feDropShadow'` | Drop shadow |

### Embedding & Animation

| Function | Description |
|----------|-------------|
| `image'` | Embedded image |
| `use'` | Use (reference) |
| `foreignObject'` | Embedded HTML |
| `animate'` | SMIL animate |
| `animateTransform'` | SMIL transform animation |
| `animateMotion'` | SMIL motion animation |
| `set'` | SMIL discrete set |
| `mpath'` | Motion path reference |

### Accessibility

| Function | Description |
|----------|-------------|
| `title'` | Accessible title |
| `desc'` | Accessible description |

```agda
open import Agdelte.Svg

-- Basic SVG with circle
myIcon : Node Model Msg
myIcon =
  svg (viewBox_ "0 0 100 100" ∷ width_ "100" ∷ height_ "100" ∷ [])
    ( circle' (cxF 50.0 ∷ cyF 50.0 ∷ rF 40.0 ∷ fillC (hex "#4a9eff") ∷ []) []
    ∷ [])
```

## Attributes

From `Agdelte.Svg.Attributes`.

All return `Attr M Msg`. `_` suffix = String, `F` suffix = Float, `C` suffix = Color.

### Geometry: Positioning

| Function | Type | Description |
|----------|------|-------------|
| `x_` / `xF` | `String` / `Float` | x position |
| `y_` / `yF` | `String` / `Float` | y position |
| `cx_` / `cxF` | `String` / `Float` | center x |
| `cy_` / `cyF` | `String` / `Float` | center y |

### Geometry: Dimensions

| Function | Type | Description |
|----------|------|-------------|
| `width_` / `widthF` | `String` / `Float` | width |
| `height_` / `heightF` | `String` / `Float` | height |
| `r_` / `rF` | `String` / `Float` | radius |
| `rx_` / `rxF` | `String` / `Float` | x radius |
| `ry_` / `ryF` | `String` / `Float` | y radius |

### Geometry: Lines

| Function | Type | Description |
|----------|------|-------------|
| `x1_` / `x1F` | `String` / `Float` | start x |
| `y1_` / `y1F` | `String` / `Float` | start y |
| `x2_` / `x2F` | `String` / `Float` | end x |
| `y2_` / `y2F` | `String` / `Float` | end y |

### Geometry: Path & Polygon

| Function | Description |
|----------|-------------|
| `d_` | Path data |
| `points_` | Polygon/polyline points |
| `viewBox_` | ViewBox attribute |
| `preserveAspectRatio_` | Aspect ratio |

### Presentation: Fill & Stroke

| Function | Type | Description |
|----------|------|-------------|
| `fill_` / `fillC` | `String` / `Color` | fill color |
| `stroke_` / `strokeC` | `String` / `Color` | stroke color |
| `strokeWidth_` / `strokeWidthF` | `String` / `Float` | stroke width |
| `fillOpacity_` / `fillOpacityF` | `String` / `Float` | fill opacity |
| `strokeOpacity_` / `strokeOpacityF` | `String` / `Float` | stroke opacity |
| `opacity_` / `opacityF` | `String` / `Float` | overall opacity |

### Presentation: Stroke Details

| Function | Description |
|----------|-------------|
| `strokeDasharray_` / `strokeDasharrayF` | Dash pattern |
| `strokeDashoffset_` / `strokeDashoffsetF` | Dash offset |
| `strokeLinecap_` | Line cap (`butt`, `round`, `square`) |
| `strokeLinejoin_` | Line join (`miter`, `round`, `bevel`) |
| `fillRule_` | Fill rule (`nonzero`, `evenodd`) |

### Transform & References

| Function | Description |
|----------|-------------|
| `transform_` | Transform string |
| `href_` | Reference (SVG 2) |
| `xlinkHref_` | Reference (SVG 1.1) |

### Text

| Function | Description |
|----------|-------------|
| `textAnchor_` | Text anchor (`start`, `middle`, `end`) |
| `dominantBaseline_` | Baseline (`auto`, `middle`, `hanging`) |
| `dx_` / `dxF` | x offset |
| `dy_` / `dyF` | y offset |
| `fontSize_` | Font size |
| `fontFamily_` | Font family |
| `fontWeight_` | Font weight |

### Gradients & Filters

| Function | Description |
|----------|-------------|
| `offset_` / `offsetF` | Gradient stop offset |
| `stopColor_` / `stopColorC` | Stop color |
| `stopOpacityF` | Stop opacity |
| `filter_` | Filter reference |
| `clipPath_` | Clip path reference |
| `mask_` | Mask reference |

## Path DSL

From `Agdelte.Svg.Path`.

### Point

```agda
record Point : Set where
  constructor _,_
  field x y : Float

showPt : Point → String
```

### Path Commands

```agda
data PathCmd : Set where
  -- Absolute commands
  M : Point → PathCmd                              -- moveTo
  L : Point → PathCmd                              -- lineTo
  H : Float → PathCmd                              -- horizontal line
  V : Float → PathCmd                              -- vertical line
  C : Point → Point → Point → PathCmd              -- cubic bezier
  S : Point → Point → PathCmd                      -- smooth cubic
  Q : Point → Point → PathCmd                      -- quadratic bezier
  T : Point → PathCmd                              -- smooth quadratic
  A : Float → Float → Float → Bool → Bool → Point → PathCmd  -- arc
  Z : PathCmd                                       -- closePath
  -- Relative commands (suffix: Rel)
  mRel lRel hRel vRel cRel sRel qRel tRel aRel : ...

Path : Set
Path = List PathCmd
```

### Rendering

| Function | Type | Description |
|----------|------|-------------|
| `renderPath` | `Path → String` | Render to `d` attribute |
| `showCmd` | `PathCmd → String` | Render single command |

### Point Operations

| Function | Type | Description |
|----------|------|-------------|
| `addPt` | `Point → Point → Point` | Add points |
| `subPt` | `Point → Point → Point` | Subtract points |
| `scalePt` | `Float → Point → Point` | Scale point |
| `dist` | `Point → Point → Float` | Distance between points |

### Path Combinators

| Function | Type | Description |
|----------|------|-------------|
| `translatePath` | `Float → Float → Path → Path` | Translate all points |
| `scalePath` | `Float → Float → Path → Path` | Scale all points |
| `closePath` | `Path → Path` | Ensure Z at end |
| `pathLength` | `Path → Float` | Estimate total length |

```agda
-- Triangle path
triangle : Path
triangle = M (0.0 , 100.0) ∷ L (50.0 , 0.0) ∷ L (100.0 , 100.0) ∷ Z ∷ []

-- Render to d attribute
path' (d_ (renderPath triangle) ∷ fillC (hex "#4a9eff") ∷ []) []
```

## Transform

From `Agdelte.Svg.Transform`.

```agda
data Transform : Set where
  translate : Float → Float → Transform
  rotate    : Float → Transform                  -- degrees
  rotateAt  : Float → Float → Float → Transform  -- degrees, cx, cy
  scale     : Float → Float → Transform          -- sx, sy
  scaleU    : Float → Transform                  -- uniform scale
  skewX     : Float → Transform                  -- degrees
  skewY     : Float → Transform                  -- degrees
  matrix    : Float → Float → Float → Float → Float → Float → Transform

Transforms : Set
Transforms = List Transform
```

| Function | Type | Description |
|----------|------|-------------|
| `renderTransform` | `Transform → String` | Render single transform |
| `renderTransforms` | `Transforms → String` | Render transform list |

```agda
-- Rotate 45 degrees around center
g (transform_ (renderTransforms (translate 50.0 50.0 ∷ rotate 45.0 ∷ [])) ∷ [])
  ( rect' (x_ "-25" ∷ y_ "-25" ∷ width_ "50" ∷ height_ "50" ∷ []) []
  ∷ [])
```

## Events

From `Agdelte.Svg.Events`.

SVG events with automatic coordinate conversion (screen → SVG space).

| Function | Type | Description |
|----------|------|-------------|
| `onSvgClick` | `(Point → Msg) → Attr M Msg` | Click with SVG coords |
| `onSvgPointerDown` | `(Point → Msg) → Attr M Msg` | Pointer down |
| `onSvgPointerMove` | `(Point → Msg) → Attr M Msg` | Pointer move |
| `onSvgPointerUp` | `Msg → Attr M Msg` | Pointer up |
| `onSvgPointerLeave` | `Msg → Attr M Msg` | Pointer leave |

```agda
-- Click handler receiving SVG coordinates
svg (onSvgClick PlacePoint ∷ viewBox_ "0 0 400 300" ∷ [])
  (...)

-- PlacePoint : Point → Msg receives coordinates in viewBox space
```

## ViewBox

From `Agdelte.Svg.ViewBox`.

```agda
record ViewBox : Set where
  constructor mkViewBox
  field minX minY width height : Float
```

| Function | Type | Description |
|----------|------|-------------|
| `showViewBox` | `ViewBox → String` | Render to string |
| `aspect` | `ViewBox → Float` | Aspect ratio |
| `panViewBox` | `Float → Float → ViewBox → ViewBox` | Pan by dx, dy |
| `zoomViewBox` | `Float → ViewBox → ViewBox` | Zoom around center |
| `zoomViewBoxAt` | `Float → Point → ViewBox → ViewBox` | Zoom at point |
| `fitViewBox` | `Float → ViewBox → ViewBox` | Fit with padding |
| `centerViewBox` | `Point → ViewBox → ViewBox` | Center on point |

### PreserveAspectRatio

```agda
data Align : Set where
  none : Align
  xMinYMin xMidYMin xMaxYMin : Align
  xMinYMid xMidYMid xMaxYMid : Align
  xMinYMax xMidYMax xMaxYMax : Align

data MeetOrSlice : Set where
  meet slice : MeetOrSlice
```

| Function | Type | Description |
|----------|------|-------------|
| `showAlign` | `Align → String` | Render alignment |
| `showMeetOrSlice` | `MeetOrSlice → String` | Render meet/slice |
| `showPAR` | `Align → MeetOrSlice → String` | Full PAR string |

```agda
-- Interactive pan/zoom
svg ( attrBind "viewBox" (stringBinding λ m → showViewBox (viewBox m))
    ∷ onSvgPointerMove (λ p → Pan p)
    ∷ [])
  (...)
```

## Gradient

From `Agdelte.Svg.Gradient`.

```agda
record GradientStop : Set where
  constructor mkStop
  field
    offset : Float   -- 0.0 to 1.0
    color  : Color
    opacity : Float  -- 0.0 to 1.0

record LinearGradient : Set where
  field id' x1 y1 x2 y2 : String ; stops : List GradientStop

record RadialGradient : Set where
  field id' cx cy r fx fy : String ; stops : List GradientStop
```

| Function | Type | Description |
|----------|------|-------------|
| `renderLinearGradient` | `LinearGradient → Node M Msg` | Render gradient def |
| `renderRadialGradient` | `RadialGradient → Node M Msg` | Render gradient def |
| `renderStop` | `GradientStop → Node M Msg` | Render stop |
| `url` | `String → String` | Generate `url(#id)` |

```agda
-- Define and use gradient
defs []
  ( renderLinearGradient (mkLinearGrad "sky" "0%" "0%" "0%" "100%"
      ( mkStop 0.0 (hex "#87CEEB") 1.0
      ∷ mkStop 1.0 (hex "#E0F7FA") 1.0
      ∷ []))
  ∷ [])
∷ rect' (fill_ (url "sky") ∷ ...) []
∷ []
```

## Filter

From `Agdelte.Svg.Filter`.

### Filter Primitives

| Function | Type | Description |
|----------|------|-------------|
| `feGaussianBlur` | `String → Float → Node M Msg` | Gaussian blur |
| `feOffset` | `String → Float → Float → Node M Msg` | Offset |
| `feBlend` | `String → String → String → Node M Msg` | Blend |
| `feFlood` | `String → Color → Float → Node M Msg` | Flood fill |
| `feComposite` | `String → String → String → String → Node M Msg` | Composite |
| `feMerge` | `String → List String → Node M Msg` | Merge |

### Presets

| Function | Description |
|----------|-------------|
| `dropShadowFilter` | Drop shadow with dx, dy, blur, color |
| `blurFilter` | Simple Gaussian blur |
| `glowFilter` | Glow effect with color |

```agda
defs []
  ( dropShadowFilter "shadow" 2.0 2.0 3.0 (rgba 0 0 0 0.3)
  ∷ [])
∷ rect' (filter_ (url "shadow") ∷ ...) []
∷ []
```

## Path Morphing

From `Agdelte.Svg.Path.Morph`.

### Interpolation

| Function | Type | Description |
|----------|------|-------------|
| `lerpFloat` | `Float → Float → Float → Float` | Lerp floats |
| `lerpPoint` | `Point → Point → Float → Point` | Lerp points |
| `lerpCmd` | `PathCmd → PathCmd → Float → PathCmd` | Lerp commands |
| `lerpPath` | `Path → Path → Float → Path` | Lerp paths |

### Line-Drawing Animation

Uses `stroke-dasharray` and `stroke-dashoffset` to animate path drawing.

| Function | Type | Description |
|----------|------|-------------|
| `drawDasharray` | `Float → String` | Dasharray for length |
| `drawDashoffset` | `Float → Float → String` | Offset for progress |
| `drawStrokeDasharray` | `Float → Attr M Msg` | Static dasharray attr |
| `drawStrokeDashoffsetBind` | `Float → (M → Float) → Attr M Msg` | Bound dashoffset |

```agda
-- Self-drawing path
path' ( d_ (renderPath myPath)
      ∷ stroke_ "#4a9eff" ∷ fill_ "none"
      ∷ drawStrokeDasharray (pathLength myPath)
      ∷ drawStrokeDashoffsetBind (pathLength myPath) (λ m → progress m)
      ∷ []) []
```

## Accessibility

From `Agdelte.Svg.Accessibility`.

### ARIA Attributes

| Function | Description |
|----------|-------------|
| `role_` | ARIA role |
| `ariaLabel_` | Accessible label |
| `ariaLabelledby_` | Label reference |
| `ariaDescribedby_` | Description reference |
| `ariaHidden_` | Hide from screen readers |
| `focusable_` | Focusable state |
| `tabindex_` | Tab index |

### Helpers

| Function | Description |
|----------|-------------|
| `accessibleSvg` | SVG with title + description |
| `decorativeSvg` | SVG hidden from screen readers |
| `graphicSvg` | SVG with aria-label |
| `svgButton` | Interactive button-like element |
| `svgLink` | Link element |

```agda
-- Accessible chart
accessibleSvg "Sales Chart" "Monthly sales data for 2024"
  (viewBox_ "0 0 400 300" ∷ [])
  (... chart content ...)

-- Decorative icon (hidden from screen readers)
decorativeSvg (width_ "16" ∷ height_ "16" ∷ [])
  (path' (d_ iconPath ∷ []) [] ∷ [])
```

## SMIL Animations

From `Agdelte.Svg.Smil`.

Declarative animations without JavaScript. Browser handles timing and interpolation.

### Duration

```agda
data Duration : Set where
  ms    : ℕ → Duration          -- milliseconds
  sec   : Float → Duration      -- seconds
  indefinite' : Duration        -- infinite
```

### Timing

```agda
data Timing : Set where
  offset     : Duration → Timing              -- delay
  onEvent    : String → Timing                -- "click", "mouseover"
  syncBegin  : String → Timing                -- "otherId.begin"
  syncBeginD : String → Duration → Timing     -- "otherId.begin+1s"
  syncEnd    : String → Timing                -- "otherId.end"
  syncEndD   : String → Duration → Timing     -- "otherId.end+500ms"
  syncRepeat : String → ℕ → Timing            -- "otherId.repeat(2)"
  anyOf      : List Timing → Timing           -- first to trigger
```

### Animation Options

```agda
data CalcMode : Set where
  discrete linear paced spline : CalcMode

data RepeatCount : Set where
  times : ℕ → RepeatCount
  indefiniteR : RepeatCount

data FillMode : Set where
  remove freeze : FillMode

data Additive : Set where
  replace sum' : Additive

data Restart : Set where
  always whenNotActive never' : Restart
```

### SmilAnim Record

```agda
record SmilAnim : Set where
  field
    dur         : Duration
    begin'      : Timing
    repeatCount : RepeatCount
    fill'       : FillMode
    additive    : Additive
    calcMode    : CalcMode
    restart     : Restart
    animId      : String

defaultSmil : SmilAnim  -- 1 second, start immediately, play once
```

### Animation Elements

| Function | Type | Description |
|----------|------|-------------|
| `animate` | `String → String → String → SmilAnim → Node M Msg` | Attribute animation |
| `animateValues` | `String → List String → SmilAnim → Node M Msg` | Keyframe animation |
| `animateTransform` | `TransformType → String → String → SmilAnim → Node M Msg` | Transform animation |
| `animateMotion` | `String → Bool → SmilAnim → Node M Msg` | Motion along path |
| `smilSet` | `String → String → SmilAnim → Node M Msg` | Discrete set |

### Choreography Helpers

| Function | Description |
|----------|-------------|
| `after` | Start after another animation ends |
| `withAnim` | Start with another animation |
| `onClick'` | Start on click |
| `loop` | Repeat indefinitely |
| `freezeEnd` | Freeze at end state |
| `withId` | Set animation ID |

```agda
-- Fade in → pulse → color shift sequence
circle' (cxF 50.0 ∷ cyF 50.0 ∷ rF 20.0 ∷ opacity_ "0" ∷ [])
  ( animate "opacity" "0" "1"
      (freezeEnd (withId "fadeIn" defaultSmil))
  ∷ animateValues "r" ("20" ∷ "25" ∷ "20" ∷ [])
      (record defaultSmil { dur = ms 400 ; begin' = syncEnd "fadeIn" })
  ∷ [])

-- Continuous rotation
g []
  ( rect' (x_ "-20" ∷ y_ "-20" ∷ width_ "40" ∷ height_ "40" ∷ []) []
  ∷ animateTransform rotateT "0" "360"
      (loop (record defaultSmil { dur = sec 3.0 }))
  ∷ [])

-- Click to expand
circle' (cxF 50.0 ∷ cyF 50.0 ∷ rF 10.0 ∷ [])
  ( animate "r" "10" "30"
      (freezeEnd (onClick' (record defaultSmil { dur = ms 200 })))
  ∷ [])
```

## Namespace Handling

The runtime automatically handles SVG namespace:

- `<svg>` switches to SVG namespace (`http://www.w3.org/2000/svg`)
- All children inherit SVG namespace
- `<foreignObject>` switches back to HTML namespace
- `xlink:href` and `xml:lang` use `setAttributeNS`

No manual namespace management needed - just use the element constructors.

## Example: Interactive Chart

```agda
open import Agdelte.Svg

record Model : Set where
  field dataPoints : List Float

barChart : Node Model Msg
barChart =
  svg (viewBox_ "0 0 400 200" ∷ width_ "400" ∷ height_ "200" ∷ [])
    ( -- Background
      rect' (width_ "400" ∷ height_ "200" ∷ fillC (hex "#f8f9fa") ∷ []) []
    ∷ -- Bars via foreach
      foreach (λ m → zipWithIndex (λ v i → (v , i)) (dataPoints m))
        (λ (val , idx) _ →
          rect' ( xF (toFloat idx * 50.0 + 10.0)
                ∷ attrBind "y" (stringBinding λ _ → showFloat (200.0 - val * 2.0))
                ∷ widthF 40.0
                ∷ attrBind "height" (stringBinding λ _ → showFloat (val * 2.0))
                ∷ fillC (hex "#4a9eff")
                ∷ []) [])
    ∷ [])
```

## File Structure

```
src/Agdelte/Svg/
  Elements.agda       -- Element constructors
  Attributes.agda     -- Attribute helpers
  Path.agda           -- Path DSL
  Path/
    Morph.agda        -- Path interpolation, line-drawing
  Transform.agda      -- Transform composition
  Events.agda         -- SVG coordinate events
  ViewBox.agda        -- ViewBox helpers
  Gradient.agda       -- Gradient definitions
  Filter.agda         -- Filter primitives
  Accessibility.agda  -- ARIA attributes, a11y helpers
  Smil.agda           -- SMIL animations

src/Agdelte/Svg.agda  -- Re-exports all modules
```

## Performance Considerations

### Large SVGs (1000+ elements)

`foreach` with 1000 data points creates 1000 elements, each with reactive bindings:
- Initial render: 1000 `createElementNS` calls
- Each update: 1000 binding checks

**Mitigations:**
- `scope`/`scopeProj` on SVG subtrees to skip unchanged regions
- `foreachKeyed` for efficient add/remove (no full rebuild)
- For 10K+ points, consider Canvas instead of SVG

### Binding Granularity

One `attrBind` per attribute means fine-grained updates. For real-time streaming data, consider a coarser approach: a single `attrBind "d"` on a `<path>` element that renders all points as one path string.

```agda
-- Skip updating the legend when only data changes
scope (λ m → show (length (getData m)))
  (g [] (foreach getData renderDataPoint ∷ []))
```

## Integration with Other Modules

### CSS Module

Shares `Color` type. SVG `fill`/`stroke` accept the same colors. CSS `@keyframes` can animate SVG presentation attributes. `Stylesheet` rules target SVG elements by class.

### Anim Module

`Spring`/`Tween` drive SVG attributes via `attrBind`. Interactive pan/zoom on viewBox, smooth path morphing, spring-driven transforms. Existing `tickSpring`/`tickTween` work directly with SVG floats.

### Agent Module

An interactive SVG visualization is an Agent: position/zoom/selection is state, mouse events are input, rendered SVG is output. Composable via standard wiring (`>>>`, `***`).

## Known Limitations

### Nesting Validation

`Node` is untyped regarding nesting. Nothing prevents putting `<div>` inside `<circle>`. The browser silently ignores invalid children. Smart constructors provide soft protection: shape elements with `[]` children by convention.

### Text Measurement

SVG text metrics (`getComputedTextLength()`) require the DOM. Auto-sizing text boxes can't be computed in Agda. Would need a `Cmd` variant for runtime measurement.

### Not Yet Implemented

From the design document, these helper modules are planned but not yet implemented:
- `Path/Generators.agda` - `regularPolygon`, `star`, `sineWave`, `circleApprox`
- `Text.agda` - `multilineText`, `textOnPath`
- `Pattern.agda` - `hatchPattern`, `dotGrid`
- `Marker.agda` - `arrowMarker`, `dotMarker`
- `Render.agda` - Static `.svg` file generation
