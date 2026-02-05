# CSS as a typed DSL with string escape hatch

## Current state

CSS in Agdelte is a pair of strings:

```agda
style : String → String → Attr Model Msg     -- style "prop" "value"
styleBind : String → Binding Model String → Attr Model Msg
```

Smart alias:

```agda
styles : String → String → Attr Model Msg
styles = style
```

Runtime hack in `dom.js`: if value contains `;`, it parses extra declarations:

```agda
styles "max-width" "500px; margin: 40px auto; font-family: sans-serif"
--     ^one prop    ^multiple declarations smuggled in the value
```

This works, but:
- No validation -- typo in property name is silent
- No composition -- styles are flat list of `Attr`, can't reuse a "group"
- Semicolon hack is fragile, depends on runtime parsing
- No media queries, pseudo-classes, keyframes, variables

## Design goal

A typed CSS layer that:
1. Catches property/value mismatches at compile time
2. Composes: style groups, mixins, conditional styles
3. Keeps `String → String` as escape hatch (always available)
4. Generates `style` attrs -- no new runtime concepts needed
5. Works incrementally -- adopt one property at a time

## Phase 1: Style record (composition without types)

The simplest improvement: a `Style` type that is a list of property-value
pairs, with a function that converts it to `List (Attr Model Msg)`.

```agda
-- A single CSS declaration
record Decl : Set where
  constructor _∶_
  field
    prop : String
    val  : String

-- A style is a list of declarations
Style : Set
Style = List Decl

-- Convert to attributes
toAttrs : ∀ {Model Msg} → Style → List (Attr Model Msg)
toAttrs = map (λ d → style (Decl.prop d) (Decl.val d))

-- Compose: merge two styles (later declarations win)
_<>_ : Style → Style → Style
_<>_ = _++_
```

Usage:

```agda
cardBase : Style
cardBase =
    "padding"       ∶ "16px"
  ∷ "border-radius" ∶ "8px"
  ∷ "background"    ∶ "white"
  ∷ []

cardShadow : Style
cardShadow =
    "box-shadow" ∶ "0 2px 8px rgba(0,0,0,0.1)"
  ∷ []

card : Style
card = cardBase <> cardShadow

-- In template:
div (class "card" ∷ toAttrs card)
    [ text "Hello" ]
```

String escape hatch is automatic: `Decl` is just `String × String`.
Any CSS, including future properties, works immediately:

```agda
"container-type" ∶ "inline-size"   -- works today, no DSL update needed
```

### Reactive styles in Phase 1

```agda
-- Dynamic style: property is static, value depends on model
dynDecl : ∀ {Model} → String → (Model → String) → DynDecl Model
dynDecl prop f = mkDynDecl prop (stringBinding f)

-- Convert to styleBind attr
toDynAttr : ∀ {Model Msg} → DynDecl Model → Attr Model Msg
toDynAttr d = styleBind (DynDecl.prop d) (DynDecl.binding d)
```

## Phase 2: Typed properties (opt-in validation)

Introduce typed wrappers for CSS values. Not a new `Attr` constructor --
just smart constructors that produce `Decl`.

### Length units

```agda
data Length : Set where
  px   : ℕ → Length
  rem  : Float → Length
  em   : Float → Length
  pct  : Float → Length      -- percent
  vh   : Float → Length
  vw   : Float → Length
  zero : Length

showLength : Length → String
showLength (px n)  = show n ++ "px"
showLength (rem f) = showFloat f ++ "rem"
showLength (em f)  = showFloat f ++ "em"
showLength (pct f) = showFloat f ++ "%"
showLength zero    = "0"
-- ...
```

### Color

```agda
data Color : Set where
  hex     : String → Color            -- "#ff0000"
  rgb     : ℕ → ℕ → ℕ → Color
  rgba    : ℕ → ℕ → ℕ → Float → Color
  hsl     : ℕ → ℕ → ℕ → Color
  named   : String → Color            -- "red", "transparent"
  var     : String → Color            -- CSS custom property
  raw     : String → Color            -- escape hatch

showColor : Color → String
showColor (hex s)       = s
showColor (rgb r g b)   = "rgb(" ++ show r ++ "," ++ show g ++ "," ++ show b ++ ")"
showColor (rgba r g b a) = "rgba(" ++ show r ++ "," ++ show g ++ "," ++ show b ++ "," ++ showFloat a ++ ")"
showColor (named s)     = s
showColor (var s)       = "var(--" ++ s ++ ")"
showColor (raw s)       = s
```

### Typed property constructors

These return `Decl`, so they compose with Phase 1's `Style`:

```agda
padding' : Length → Decl
padding' l = "padding" ∶ showLength l

padding2 : Length → Length → Decl
padding2 v h = "padding" ∶ showLength v ++ " " ++ showLength h

padding4 : Length → Length → Length → Length → Decl
padding4 t r b l = "padding" ∶ showLength t ++ " " ++ showLength r ++ " " ++ showLength b ++ " " ++ showLength l

color' : Color → Decl
color' c = "color" ∶ showColor c

background' : Color → Decl
background' c = "background" ∶ showColor c

fontSize' : Length → Decl
fontSize' l = "font-size" ∶ showLength l
```

Mixing typed and untyped in one `Style`:

```agda
myStyle : Style
myStyle =
    padding' (rem 1.0)
  ∷ color' (hex "#333")
  ∷ "font-family" ∶ "system-ui, sans-serif"    -- raw string, no wrapper needed
  ∷ "grid-template" ∶ "1fr auto / 1fr 1fr"     -- complex value, use raw
  ∷ []
```

## Phase 3: Conditional & responsive styles

### Conditional styles

```agda
-- Choose style based on condition (at template construction time)
styleIf : Bool → Style → Style
styleIf true  s = s
styleIf false _ = []

-- Merge with override
styleWhen : Bool → Style → Style → Style
styleWhen true  active _       = active
styleWhen false _      fallback = fallback
```

For model-dependent styles, two paths:

**Path A: model-time choice (template is rebuilt per item)**

Already works in `foreach`/`foreachKeyed` because the render function
receives the item:

```agda
viewItem : Item → ℕ → Node Model Msg
viewItem item _ =
  div (toAttrs (baseStyle <> styleIf (active item) activeHighlight))
      [ text (name item) ]
```

**Path B: binding-time choice (single node, style changes reactively)**

Use `styleBind` with a function that returns the value:

```agda
-- Background depends on model
bgBinding : Binding Model String
bgBinding = stringBinding λ m →
  if isError m then "#fee" else "#fff"

div (styleBind "background" bgBinding ∷ toAttrs baseStyle)
    [ ... ]
```

### Responsive (future, requires runtime support)

Responsive styles need `@media` queries or `matchMedia` listener. Two
possible approaches:

**A. CSS class approach (no runtime change):**

Generate a `<style>` element with media queries referencing classes.
Template uses `class`. This is the Web-standard approach and doesn't
require new Agda types.

```agda
-- Agda generates a stylesheet string at init time
appStylesheet : String
appStylesheet = """
  .card { padding: 16px; }
  @media (max-width: 768px) {
    .card { padding: 8px; }
  }
"""
```

Runtime injects it as `<style>` on mount. Template uses `class "card"`.

**B. matchMedia subscription (model-driven):**

Add a subscription that fires a `Msg` on viewport change. Model stores
current breakpoint. Styles are computed from model. This works with
existing `styleBind` -- no CSS DSL changes needed, only a new `Sub`.

```agda
data Breakpoint : Set where
  mobile tablet desktop : Breakpoint

onResize : (Breakpoint → Msg) → Sub Msg

-- In template:
styleBind "padding" (stringBinding λ m →
  case breakpoint m of
    mobile  → "8px"
    tablet  → "12px"
    desktop → "16px")
```

Recommendation: start with **A** (CSS classes + generated stylesheet).
It uses the browser's native responsive system and requires zero runtime
changes.

## Phase 4: CSS custom properties (variables)

CSS custom properties are just regular style declarations on a parent
element. No special support needed:

```agda
themeVars : Style
themeVars =
    "--primary"    ∶ "#3b82f6"
  ∷ "--bg"         ∶ "#ffffff"
  ∷ "--text"       ∶ "#1a1a1a"
  ∷ "--radius"     ∶ "8px"
  ∷ []

-- Use with var()
card : Style
card =
    "background"    ∶ "var(--bg)"
  ∷ "color"         ∶ "var(--text)"
  ∷ "border-radius" ∶ "var(--radius)"
  ∷ []
```

Dynamic theming -- `styleBind` on the root element:

```agda
-- Model has isDark : Bool
styleBind "--primary" (stringBinding λ m →
  if isDark m then "#60a5fa" else "#3b82f6")
```

The runtime already supports this: `el.style.setProperty("--primary", value)`
works for custom properties.

## Phase 5: Stylesheet generation

For styles that don't depend on model (static CSS), it's more efficient
to generate a `<style>` block than to set inline styles per element.

```agda
data Rule : Set where
  rule     : String → Style → Rule                -- .class { ... }
  media    : String → List Rule → Rule            -- @media (...) { ... }
  keyframe : String → List (String × Style) → Rule  -- @keyframes name { from { } to { } }

Stylesheet : Set
Stylesheet = List Rule

renderStylesheet : Stylesheet → String
```

Usage:

```agda
appCSS : Stylesheet
appCSS =
    rule ".card" (
        padding' (rem 1.0)
      ∷ background' (hex "#fff")
      ∷ "border-radius" ∶ "8px"     -- raw string, always works
      ∷ [])
  ∷ rule ".card:hover" (
        "box-shadow" ∶ "0 4px 12px rgba(0,0,0,0.15)"
      ∷ [])
  ∷ media "(max-width: 768px)" (
        rule ".card" (
            padding' (px 8)
          ∷ [])
      ∷ [])
  ∷ keyframe "fadeIn" (
        ("from" , "opacity" ∶ "0" ∷ [])
      ∷ ("to"   , "opacity" ∶ "1" ∷ [])
      ∷ [])
  ∷ []
```

Template uses `class`:

```agda
div (class "card" ∷ []) [ text "Hello" ]
```

Runtime mounts stylesheet once (a `<style>` element in `<head>`). This
combines with `whenT` transitions naturally -- the keyframe and class
names are just strings.

### String escape hatch for entire rules

```agda
rawRule : String → Rule
rawRule s = ...    -- inject literal CSS text

-- For CSS features the DSL hasn't covered yet:
rawRule "@layer components { .card { container-type: inline-size; } }"
```

## Phase 6: Flexbox / Grid helpers (sugar)

Convenience functions that produce `Style`:

```agda
-- Flexbox
row : Style
row = "display" ∶ "flex" ∷ "flex-direction" ∶ "row" ∷ []

col : Style
col = "display" ∶ "flex" ∷ "flex-direction" ∶ "column" ∷ []

center : Style
center = "justify-content" ∶ "center" ∷ "align-items" ∶ "center" ∷ []

spaceBetween : Style
spaceBetween = "justify-content" ∶ "space-between" ∷ []

gap' : Length → Style
gap' l = "gap" ∶ showLength l ∷ []

-- Grid
grid : String → Style
grid template = "display" ∶ "grid" ∷ "grid-template" ∶ template ∷ []

-- Common patterns
stack : Length → Style          -- vertical stack with gap
stack g = col <> gap' g

inline : Length → Style         -- horizontal row with gap
inline g = row <> gap' g
```

Usage:

```agda
div (toAttrs (row <> center <> gap' (px 12)))
    ( button [] [ text "A" ]
    ∷ button [] [ text "B" ]
    ∷ [] )
```

## Phase 7: CSS animations

Animations split into two categories: **transitions** (A → B on property
change) and **keyframe animations** (multi-step, named, reusable).

### Transitions (typed shorthand)

CSS `transition` is a string: `"opacity 0.3s ease, transform 0.2s"`.
A typed DSL makes this composable:

```agda
data Easing : Set where
  ease linear easeIn easeOut easeInOut : Easing
  cubicBezier : Float → Float → Float → Float → Easing
  raw : String → Easing                     -- escape hatch

showEasing : Easing → String
showEasing ease       = "ease"
showEasing linear     = "linear"
showEasing easeInOut  = "ease-in-out"
showEasing (cubicBezier a b c d) =
  "cubic-bezier(" ++ showFloat a ++ "," ++ showFloat b ++ ","
                  ++ showFloat c ++ "," ++ showFloat d ++ ")"
showEasing (raw s)    = s

data Duration : Set where
  ms : ℕ → Duration
  s  : Float → Duration

showDuration : Duration → String
showDuration (ms n) = show n ++ "ms"
showDuration (s f)  = showFloat f ++ "s"

-- A single transition spec
record TransSpec : Set where
  constructor mkTransSpec
  field
    property : String
    dur      : Duration
    easing   : Easing
    delay    : Duration     -- default: ms 0

-- Convenience constructor (no delay)
trans : String → Duration → Easing → TransSpec
trans p d e = mkTransSpec p d e (ms 0)

-- Render list of TransSpec to a single Decl
transition' : List TransSpec → Decl
transition' specs = "transition" ∶ renderSpecs specs
  where
    renderSpec : TransSpec → String
    renderSpec t = TransSpec.property t ++ " "
               ++ showDuration (TransSpec.dur t) ++ " "
               ++ showEasing (TransSpec.easing t)
               ++ (case TransSpec.delay t of
                     ms 0 → ""
                     d    → " " ++ showDuration d)

    renderSpecs : List TransSpec → String
    renderSpecs = intercalate ", " ∘ map renderSpec
```

Usage:

```agda
cardStyle : Style
cardStyle =
    "opacity"    ∶ "1"
  ∷ "transform"  ∶ "scale(1)"
  ∷ transition' ( trans "opacity" (ms 300) ease
                ∷ trans "transform" (ms 200) easeOut
                ∷ [])
  ∷ []

cardHover : Style
cardHover =
    "opacity"   ∶ "0.9"
  ∷ "transform" ∶ "scale(1.02)"
  ∷ []
```

The typed layer prevents `"esae"` typos in easing and `"30ms0"` in
duration. Raw escape hatch always works:

```agda
transition' ( mkTransSpec "all" (ms 300) (raw "steps(4, end)") (ms 0) ∷ [])
-- or just:
"transition" ∶ "all 300ms steps(4, end)"
```

### Keyframe animations (typed)

Phase 5 has `keyframe` in `Rule`. Here we add a typed DSL for the
animation shorthand and multi-step keyframes:

```agda
-- Keyframe stop: percentage (0-100) or from/to aliases
data Stop : Set where
  at   : ℕ → Stop          -- at 50 = "50%"
  from : Stop               -- = at 0
  to   : Stop               -- = at 100

showStop : Stop → String
showStop (at n) = show n ++ "%"
showStop from   = "from"
showStop to     = "to"

-- A keyframe is a named sequence of stops with styles
record Keyframes : Set where
  constructor mkKeyframes
  field
    name  : String
    stops : List (Stop × Style)

-- Render to @keyframes rule
renderKeyframes : Keyframes → String
-- renderKeyframes (mkKeyframes "fadeSlide" stops) =
--   "@keyframes fadeSlide { 0% { opacity: 0; ... } 100% { ... } }"
```

Multi-step example:

```agda
pulse : Keyframes
pulse = mkKeyframes "pulse"
    ( (from , "transform" ∶ "scale(1)"   ∷ "opacity" ∶ "1"   ∷ [])
    ∷ (at 50, "transform" ∶ "scale(1.05)" ∷ "opacity" ∶ "0.8" ∷ [])
    ∷ (to   , "transform" ∶ "scale(1)"   ∷ "opacity" ∶ "1"   ∷ [])
    ∷ [])

shake : Keyframes
shake = mkKeyframes "shake"
    ( (at 0  , "transform" ∶ "translateX(0)"    ∷ [])
    ∷ (at 25 , "transform" ∶ "translateX(-4px)" ∷ [])
    ∷ (at 50 , "transform" ∶ "translateX(4px)"  ∷ [])
    ∷ (at 75 , "transform" ∶ "translateX(-4px)" ∷ [])
    ∷ (at 100, "transform" ∶ "translateX(0)"    ∷ [])
    ∷ [])
```

### Animation shorthand

```agda
data FillMode : Set where
  none forwards backwards both : FillMode

data Direction : Set where
  normal reverse alternate alternateReverse : Direction

data IterCount : Set where
  times    : ℕ → IterCount
  infinite : IterCount

record Animation : Set where
  constructor mkAnim
  field
    name      : String
    dur       : Duration
    easing    : Easing
    delay     : Duration
    count     : IterCount
    direction : Direction
    fillMode  : FillMode

-- Sensible defaults
anim : String → Duration → Animation
anim n d = mkAnim n d ease (ms 0) (times 1) normal none

-- Render to Decl
animation' : Animation → Decl
animation' a = "animation" ∶ renderAnimation a

-- Render to Style (multiple animations on one element)
animations : List Animation → Decl
animations = ...   -- comma-separated
```

Usage:

```agda
-- Simple fade-in
fadeInStyle : Style
fadeInStyle = animation' (anim "fadeIn" (ms 300)) ∷ []

-- Infinite pulse with easeInOut
pulseStyle : Style
pulseStyle =
  let a = anim "pulse" (s 2.0)
  in animation' (record a { count = infinite ; easing = easeInOut }) ∷ []

-- Shake on error, don't repeat
errorShake : Style
errorShake =
  animation' (record (anim "shake" (ms 400))
    { easing = easeOut ; fillMode = forwards }) ∷ []
```

### Integration with whenT

`whenT` already manages enter/leave CSS classes. Animations compose
naturally: define keyframes in the stylesheet, reference them in enter/
leave classes.

```agda
-- Stylesheet (Phase 5):
appCSS : Stylesheet
appCSS =
    keyframe "slideDown" (
        (from , "opacity" ∶ "0" ∷ "transform" ∶ "translateY(-20px)" ∷ [])
      ∷ (to   , "opacity" ∶ "1" ∷ "transform" ∶ "translateY(0)"    ∷ [])
      ∷ [])
  ∷ keyframe "slideUp" (
        (from , "opacity" ∶ "1" ∷ "transform" ∶ "translateY(0)"    ∷ [])
      ∷ (to   , "opacity" ∶ "0" ∷ "transform" ∶ "translateY(-20px)" ∷ [])
      ∷ [])
  ∷ rule ".panel-enter" (
        animation' (record (anim "slideDown" (ms 300)) { easing = easeOut })
      ∷ [])
  ∷ rule ".panel-leave" (
        animation' (record (anim "slideUp" (ms 300)) { easing = easeIn })
      ∷ [])
  ∷ []

-- Template:
panelTrans : Transition
panelTrans = mkTransition "panel-enter" "panel-leave" 300

whenT showPanel panelTrans
    (div (toAttrs cardStyle) [ text "Content" ])
```

No runtime change. `whenT` adds the class, the browser runs the animation.

### Model-driven animations

For animations triggered by model changes (not show/hide), use
`styleBind` on the `animation` property:

```agda
-- Trigger shake when model has error
styleBind "animation" (stringBinding λ m →
  if hasError m then "shake 0.4s ease" else "none")
```

Caveat: re-triggering the same animation requires removing and re-adding
it. The runtime can handle this by detecting same-value → briefly set
`"none"` → set animation again on next frame. This is a small runtime
addition:

```javascript
// In reactive.js, style binding update:
if (styleName === 'animation' && newVal === lastValue && newVal !== 'none') {
  el.style.animation = 'none';
  requestAnimationFrame(() => { el.style.animation = newVal; });
  return;  // don't skip -- we need the re-trigger
}
```

### Transition + animation library (presets)

Common animations as ready-made `Keyframes` + `Animation` pairs:

```agda
module Agdelte.Css.Animate where

-- Entrances
fadeIn fadeInUp fadeInDown fadeInLeft fadeInRight : Keyframes
slideInUp slideInDown slideInLeft slideInRight   : Keyframes
scaleIn zoomIn : Keyframes

-- Exits (reverse of entrances)
fadeOut fadeOutUp fadeOutDown : Keyframes
slideOutUp slideOutDown      : Keyframes
scaleOut zoomOut : Keyframes

-- Attention seekers
pulse bounce shake wobble flash : Keyframes

-- Loops
spin rotate swing : Keyframes

-- Convenience: keyframes + matching animation with sensible duration
fadeInAnim : Duration → Animation
fadeInAnim d = anim "fadeIn" d

-- Ready-made transition pair for whenT
fadeTransition : ℕ → Transition × List Rule
fadeTransition dur =
  mkTransition "fade-enter" "fade-leave" dur
  , rule ".fade-enter" (animation' (anim "fadeIn" (ms dur)) ∷ [])
  ∷ rule ".fade-leave" (animation' (anim "fadeOut" (ms dur)) ∷ [])
  ∷ []

slideTransition : ℕ → Transition × List Rule
slideTransition dur = ...
```

Usage:

```agda
open import Agdelte.Css.Animate

-- One-liner: get Transition + CSS rules
fadePair  = fadeTransition 300
slidePair = slideTransition 400

-- In stylesheet:
appCSS = snd fadePair ++ snd slidePair ++ otherRules

-- In template:
whenT showPanel (fst fadePair)
    (div [] [ text "Fading panel" ])
```

### Staggered list animations

For `foreach`/`foreachKeyed` items that animate in sequence:

```agda
-- Each item gets increasing animation-delay
staggerDelay : ℕ → ℕ → Decl
staggerDelay index stepMs = "animation-delay" ∶ showDuration (ms (index * stepMs))

viewItem : Item → ℕ → Node Model Msg
viewItem item idx =
  li (toAttrs (
        animation' (anim "fadeInUp" (ms 300))
      ∷ staggerDelay idx 50                    -- 0ms, 50ms, 100ms, ...
      ∷ "animation-fill-mode" ∶ "both"
      ∷ []))
    [ text (name item) ]
```

The `ℕ` index is already available as the second argument of `foreach`
and `foreachKeyed` render functions. No runtime change needed.

### Runtime: Web Animations API (future)

CSS animations have limitations (can't read current value, hard to
chain, no spring physics). The Web Animations API gives programmatic
control:

```javascript
el.animate([
  { transform: 'translateY(-20px)', opacity: 0 },
  { transform: 'translateY(0)',     opacity: 1 }
], { duration: 300, easing: 'ease-out' });
```

This could be exposed as a `Cmd`:

```agda
data AnimCmd : Set where
  animateEl : String → List (String × Style) → AnimOpts → AnimCmd
  --          ^selector  ^keyframe stops       ^duration, easing, etc.

-- In update:
update : Msg → Model → Model × Cmd Msg
update ShowResult m = record m { visible = true }
  , animate "#result" fadeInStops (mkOpts (ms 300) easeOut)
```

This is a substantial addition (new Cmd variant, runtime handler,
element lookup by selector or ref). Defer until CSS animations prove
insufficient. For most UI work, CSS `@keyframes` + `animation` +
`transition` cover 95% of cases.

## Phase 8: Model-driven animations (FRP path)

CSS animations are fire-and-forget: the browser interpolates, Agda
doesn't see intermediate values. This is fine for presentation polish
(fade, slide, hover glow). But when the intermediate state matters --
physics, springs, drag, scroll-linked, interactive particles -- the
animation must live in the model.

### Two animation worlds

```
CSS world (browser)                 Model world (Agdelte)
───────────────────────             ─────────────────────────
animation: fadeIn 300ms             animationFrame → dt → update → styleBind
runs on GPU / compositor            runs on main thread (JS)
invisible to model                  observable, in model
can't compose with logic            composable (Agent combinators)
no physics / springs                spring, drag, particles
can't replay                        deterministic replay
```

**Boundary rule:** if the intermediate value doesn't affect application
logic, use CSS. If it does, use model.

### Animation as coalgebra

An animation is an Agent. This is not an analogy -- it's the same type:

```agda
-- Animation: state machine with dt input, current value output
-- Coalgebra of p(y) = Float × y^ℕ
--   Pos = Float   (current value)
--   Dir = ℕ       (dt in milliseconds)

-- Tween is Agent TweenState ℕ Float
-- Spring is Agent SpringState ℕ Float
```

This means animations get _all_ Agent combinators for free:

```agda
-- Sequential: fadeIn then slideDown
fadeIn >>> slideDown

-- Parallel: opacity and transform simultaneously
fadeIn *** slideRight

-- Choice: animate A or B depending on state
fadeIn & shake
```

### Tween

Linear interpolation from A to B over time, with easing.

```agda
record Tween (A : Set) : Set where
  constructor mkTween
  field
    elapsed  : ℕ          -- ms elapsed so far
    duration : ℕ          -- total ms
    from     : A
    to       : A
    easing   : Float → Float    -- same Easing as CSS (shared type!)
    lerp     : A → A → Float → A

tickTween : Tween A → ℕ → Tween A × A
tickTween t dt =
  let e' = min (elapsed t + dt) (duration t)
      progress = easing t (toFloat e' / toFloat (duration t))
      value = lerp t (from t) (to t) progress
  in record t { elapsed = e' } , value

isComplete : Tween A → Bool
isComplete t = elapsed t >= duration t
```

`Easing` is the same type as in Phase 7 (`Css.Easing`). One module,
two consumers: CSS `transition` shorthand and model `Tween`.

### Spring

The killer feature CSS can't do. A spring is real physics:

```agda
record Spring : Set where
  constructor mkSpring
  field
    position  : Float
    velocity  : Float
    target    : Float
    stiffness : Float    -- spring constant (higher = snappier)
    damping   : Float    -- friction (higher = less bounce)

tickSpring : Spring → ℕ → Spring
tickSpring s dt =
  let dtSec = toFloat dt / 1000.0
      force = stiffness s * (target s - position s)
            - damping s * velocity s
      v' = velocity s + force * dtSec
      p' = position s + v' * dtSec
  in record s { position = p' ; velocity = v' }

-- Spring is settled when position ≈ target and velocity ≈ 0
isSettled : Spring → Bool
isSettled s = abs (position s - target s) < 0.01
            ∧ abs (velocity s) < 0.01
```

Presets:

```agda
-- iOS-like smooth spring
gentle : Float → Float → Spring
gentle from to = mkSpring from 0.0 to 120.0 14.0

-- Snappy, minimal overshoot
snappy : Float → Float → Spring
snappy from to = mkSpring from 0.0 to 400.0 28.0

-- Bouncy, playful
bouncy : Float → Float → Spring
bouncy from to = mkSpring from 0.0 to 180.0 8.0
```

### Sequence and parallel

Since Tween and Spring are Agents, composition is direct:

```agda
-- Sequential: run animations one after another
-- When first completes, start second
sequenceAnim : List (Tween A) → SequenceAgent A

-- Parallel: run multiple animations, output tuple
-- fadeIn *** slideRight : Agent (Tween Float × Tween Float) ℕ (Float × Float)

-- Stagger: same animation with increasing delay per item
staggerAnim : ℕ → ℕ → Tween A → List (Tween A)
staggerAnim count delayMs base =
  map (λ i → record base { elapsed = negate (i * delayMs) }) (range count)
  -- negative elapsed = hasn't started yet, counts up until 0 then animates
```

### Wiring to template

The standard pattern: subscription + update + styleBind.

```agda
-- Model stores animation state
record Model : Set where
  field
    spring   : Spring
    menuOpen : Bool
    ...

-- Subscribe to animationFrame only when animation is active
subs : Model → Event Msg
subs m = if isSettled (spring m)
         then never                      -- idle, no cost
         else mapE AnimTick animationFrame

-- Update: advance animation
update : Msg → Model → Model
update (AnimTick dt) m = record m
  { spring = tickSpring (spring m) dt }
update ToggleMenu m = record m
  { menuOpen = not (menuOpen m)
  ; spring = record (spring m) { target = if menuOpen m then 0.0 else 250.0 }
  }

-- Template: bind spring position to CSS transform
div ( styleBind "transform" (stringBinding λ m →
        "translateX(" ++ showFloat (Spring.position (spring m)) ++ "px)")
    ∷ styles "will-change" "transform"     -- hint for GPU compositing
    ∷ [])
    [ text "Sliding panel" ]
```

Key detail: `will-change: transform` tells the browser to promote
the element to its own compositor layer. This makes `styleBind` updates
GPU-accelerated even though they're driven from JS.

### Convenience: animWhen

Reduce the subscription boilerplate:

```agda
-- Subscribe to animationFrame only when predicate is true
animWhen : (Model → Bool) → (ℕ → Msg) → Model → Event Msg
animWhen active mkMsg m =
  if active m
  then mapE mkMsg animationFrameWithDt
  else never
```

Usage:

```agda
subs m = animWhen (not ∘ isSettled ∘ spring) AnimTick m
       <|> otherSubs m
```

### Multi-property animation

Often one gesture drives multiple CSS properties (opacity + transform +
border-radius). Instead of N springs, use a single spring and derive
properties:

```agda
-- One spring drives the whole transition: 0.0 = closed, 1.0 = open
cardSpring : Spring
cardSpring = gentle 0.0 1.0

-- Derive multiple CSS properties from one progress value
cardTransform : Float → String
cardTransform t = "scale(" ++ showFloat (0.95 + 0.05 * t) ++ ")"

cardOpacity : Float → String
cardOpacity t = showFloat (0.5 + 0.5 * t)

cardRadius : Float → String
cardRadius t = showFloat (16.0 - 8.0 * t) ++ "px"

-- In template:
div ( styleBind "transform" (stringBinding (cardTransform ∘ Spring.position ∘ spring))
    ∷ styleBind "opacity" (stringBinding (cardOpacity ∘ Spring.position ∘ spring))
    ∷ styleBind "border-radius" (stringBinding (cardRadius ∘ Spring.position ∘ spring))
    ∷ [])
    [ ... ]
```

### Formal connection (Theory/)

```agda
-- In src/Agdelte/Theory/AnimCoalg.agda:

-- Tween is a coalgebra of p(y) = Float × y^ℕ
TweenAgent : Set → Set
TweenAgent A = Agent (Tween A) ℕ A

tweenToAgent : Tween A → TweenAgent A
tweenToAgent t = record
  { state   = t
  ; observe = λ s → snd (tickTween s 0)   -- current value
  ; step    = λ s dt → fst (tickTween s dt)
  }

-- Spring is the same polynomial
SpringAgent : Agent Spring ℕ Float
SpringAgent s = record
  { state   = s
  ; observe = position
  ; step    = tickSpring
  }

-- Therefore _>>>_ and _***_ from Agent compose animations
-- No new composition mechanism needed
```

## Phase 9: .css file generation (Agda as CSS compiler)

Phase 5 defines `renderStylesheet : Stylesheet → String`. That string
can go to a `<style>` element at runtime, or to a `.css` file at build
time. This phase is about the second path.

### Why .css file

| | `<style>` mount (dev) | `.css` file (prod) |
|---|---|---|
| FOUC | Yes -- styles apply after JS loads | No -- `<link>` blocks render |
| Caching | Inside JS bundle, not cached separately | Own cache key, CDN-friendly |
| Load | Sequential: JS → parse → inject | Parallel: CSS + JS load together |
| Build step | None | `node generate-css.js` |

Both use the same `renderStylesheet`. The difference is who consumes
the string.

### Build pipeline

```
MyApp/Styles.agda                   -- appCSS : Stylesheet
       │
       │  agda --js
       ▼
_build/MAlonzo/MyApp/Styles.js      -- compiled renderStylesheet + appCSS
       │
       │  node generate-css.js
       ▼
dist/app.css                         -- plain CSS, static, cacheable
dist/app.js                          -- application bundle
dist/index.html                      -- <link href="app.css"> + <script src="app.js">
```

The generator is trivial:

```javascript
// generate-css.js
import { renderStylesheet, appCSS } from './_build/MAlonzo/MyApp/Styles.js';
import { writeFileSync } from 'fs';

writeFileSync('dist/app.css', renderStylesheet(appCSS));
```

One line in `package.json`:

```json
"build:css": "node generate-css.js",
"build": "agda --js MyApp.agda && npm run build:css"
```

### What Agda gives over Sass/Less/PostCSS

Sass has variables, mixins, nesting -- syntactic sugar over strings.
No types. `$padding: red` compiles happily. `darken($size, 10%)` too.

Agda has dependent types, totality checking, and a proof system.
The stylesheet is a **verified program** that produces CSS:

- `Length` won't compose with `Color` -- type error at compile time
- `padding' : Length → Decl` won't accept a `Color` argument
- `Easing` is exhaustively pattern-matched -- no typos
- `Stylesheet` is a `List Rule` -- every rule has a selector and a
  well-formed `Style`
- Shared class name constants between stylesheet and template --
  if a class is removed from the template, the import in Styles.agda
  is unused (compiler warning)

More concretely: Sass is a macro expander that emits strings. Agda is
a proof assistant that happens to emit CSS. The gap is not incremental.

### Shared class names

Class names used in `rule` selectors are the same strings used in
template `class` attributes. Extract them to a shared module:

```agda
module MyApp.Classes where

cardClass    = "card"
btnClass     = "btn"
activeClass  = "active"
```

```agda
-- Stylesheet uses them:
module MyApp.Styles where
open import MyApp.Classes

appCSS : Stylesheet
appCSS =
    rule ("." ++ cardClass) cardStyle
  ∷ rule ("." ++ btnClass) btnStyle
  ∷ rule ("." ++ btnClass ++ "." ++ activeClass) activeBtnStyle
  ∷ []
```

```agda
-- Template uses them:
module MyApp.Template where
open import MyApp.Classes

template =
  div (class cardClass ∷ toAttrs cardInline)
    [ button (class btnClass ∷ onClick Click ∷ []) [ text "OK" ] ]
```

Remove `cardClass` from template → the import from `MyApp.Classes` is
unused in Template → compiler warning. The rule in Styles becomes dead
CSS. Not runtime tree-shaking -- **compile-time orphan detection**.

### Content hashing

`renderStylesheet` is a pure function. Same `Stylesheet` → same output →
same hash. Cache invalidation is deterministic:

```javascript
import { createHash } from 'crypto';

const css = renderStylesheet(appCSS);
const hash = createHash('md5').update(css).digest('hex').slice(0, 8);
writeFileSync(`dist/app.${hash}.css`, css);
```

### Readable vs minified

Two render modes:

```agda
renderStylesheet : Stylesheet → String     -- dev: indented, readable
renderMinified   : Stylesheet → String     -- prod: no whitespace
```

Or skip Agda-level minification entirely: pipe through `lightningcss`
or `cssnano` as a post-step. Simpler, and those tools handle browser
compat too.

### What stays in runtime

.css file = **static rules only**: classes, media queries, keyframes,
pseudo-classes, CSS variables defaults.

Everything model-dependent stays as `styleBind` in the runtime:

```
app.css (static, generated)          runtime (dynamic)
────────────────────────────         ─────────────────────────
.card { padding: 16px; ... }         styleBind "transform" (spring)
.card:hover { box-shadow: ... }      styleBind "--primary" (theme)
@keyframes fadeIn { ... }            styleBind "opacity" (tween)
@media (max-width: 768px) { ... }
```

Clean split. Static compiles to file. Dynamic is inline via bindings.

### Dev mode: `<style>` mount

In dev, rebuilding .css on every change is friction. The runtime can
mount the same `Stylesheet` as a `<style>` element:

```agda
mountStylesheet : Stylesheet → Cmd Msg
```

Same source, two outputs. Dev = runtime mount. Prod = build step → file.

## Implementation order

1. **Phase 1** -- `Decl`, `Style`, `toAttrs`, `<>`. One file, ~30 lines.
   Unlocks composition immediately.
2. **Phase 6** -- flexbox/grid helpers. Tiny, high payoff.
3. **Phase 4** -- CSS variables. Zero runtime work, just conventions.
4. **Phase 2** -- `Length`, `Color`, `Easing`, `Duration`, typed constructors.
   Opt-in, doesn't break anything.
5. **Phase 5** -- Stylesheet generation. `renderStylesheet`, runtime
   `<style>` mount. Unlocks media queries, keyframes, pseudo-classes.
6. **Phase 9** -- .css file generation. `generate-css.js`, content hash,
   `renderMinified`. Depends on Phase 5. Tiny build script.
7. **Phase 7** -- CSS animations. `Keyframes`, `Animation`, `TransSpec`,
   presets, stagger. Depends on Phase 2 types + Phase 5 stylesheet.
8. **Phase 8** -- Model animations. `Tween`, `Spring`, `isSettled`,
   `animWhen`. Depends on Phase 2 (`Easing` shared). No runtime changes.
9. **Phase 3** -- Responsive. Depends on Phase 5 or matchMedia sub.

## File structure

```
src/Agdelte/Css/
  Decl.agda         -- Decl, Style, toAttrs, <>
  Length.agda        -- Length, showLength
  Color.agda         -- Color, showColor
  Easing.agda        -- Easing, Duration, showEasing, showDuration (shared!)
  Properties.agda    -- Typed property constructors (padding', color', etc.)
  Transition.agda    -- TransSpec, transition' (CSS transition shorthand)
  Animation.agda     -- Keyframes, Animation, animation', Stop
  Animate.agda       -- Presets: fadeIn, slideIn, pulse, shake, etc.
  Layout.agda        -- Flexbox/Grid helpers (row, col, center, gap', grid)
  Stylesheet.agda    -- Rule, Stylesheet, renderStylesheet, renderMinified
  Generate.agda      -- mountStylesheet (runtime <style> mount)
  Variables.agda     -- Theme variable helpers

scripts/
  generate-css.js    -- build step: Stylesheet → .css file

src/Agdelte/Anim/
  Tween.agda        -- Tween A, tickTween, isComplete, lerp helpers
  Spring.agda       -- Spring, tickSpring, isSettled, presets (gentle, snappy, bouncy)
  Sequence.agda     -- sequenceAnim, staggerAnim (sugar over Agent >>>)
  Util.agda         -- animWhen, multi-property helpers
```

Re-exported from a single module:

```agda
module Agdelte.Css where

open import Agdelte.Css.Decl public
open import Agdelte.Css.Length public
open import Agdelte.Css.Color public
open import Agdelte.Css.Easing public
open import Agdelte.Css.Properties public
open import Agdelte.Css.Transition public
open import Agdelte.Css.Animation public
open import Agdelte.Css.Layout public
```

## Relation to other ideas

### polynomials.md

Animation as coalgebra is the key connection. `Tween` and `Spring` are
coalgebras of `p(y) = Float × y^ℕ` -- the same polynomial as
`Agent S ℕ Float`. This means all Agent combinators (`_>>>_`, `_***_`,
`_&_`) compose animations without any new mechanism. Formally provable
in `Theory/AnimCoalg.agda`.

### webgl.md

Materials are the 3D equivalent of CSS. The `Color` type from Phase 2
is shared. `Material` could accept `Color` directly. Model-driven
animations (Phase 8) are essential for 3D: camera orbits, object
transforms, skeletal animation are all springs/tweens in the model.

### concurrency.md

Stylesheet mounting is a one-time DOM operation (no batching concern).
Dynamic style bindings (`styleBind`) already go through the reactive
update path and benefit from batching. Model-driven animations generate
one `AnimTick` message per frame -- batching merges multiple
`animationFrame` events if they queue up.

### time-model.md

Phase 8 is the direct application of the time model. `animationFrame`
gives discrete `dt`, `tickTween`/`tickSpring` advance state, `styleBind`
renders. Fixed timestep pattern from time-model.md applies to spring
physics (prevents instability on lag spikes). `isSettled` / `isComplete`
control subscription -- no events when idle, battery saved.

### Transitions (existing whenT)

Phase 5's `keyframe` generation replaces hand-written CSS for
`enterClass`/`leaveClass` animations:

```agda
appCSS =
    keyframe "panel-enter" (
        ("from" , "opacity" ∶ "0" ∷ "transform" ∶ "translateY(-10px)" ∷ [])
      ∷ ("to"   , "opacity" ∶ "1" ∷ "transform" ∶ "translateY(0)" ∷ [])
      ∷ [])
  ∷ rule ".panel-enter" (
        "animation" ∶ "panel-enter 0.3s ease"
      ∷ [])
  ∷ []
```

## Open questions

1. Should `Style` be a record with `_<>_` as a monoid, or just `List Decl`?
   List is simpler. Monoid gives better inference for `mempty`.
2. Should duplicate properties in `_<>_` be deduplicated (last wins)?
   CSS itself does this, so maybe not necessary. But it affects
   `styleBind` if the same property is set both statically and dynamically.
3. Should `toAttrs` emit one `style` attr per declaration, or pack
   them into a single string? Current runtime handles both. One-per-decl
   is cleaner for reactive overrides.
4. Should the `Stylesheet` be compiled to a string at Agda level (pure)
   or at runtime (JS)? Both -- see Phase 9. Pure for .css file
   generation (build step). Runtime for dev mode (`<style>` mount).
5. How to handle vendor prefixes (`-webkit-`, `-moz-`)? Probably ignore --
   browsers have converged.
6. Should animation re-trigger logic (remove + re-add on same value) be
   in the runtime or handled by the user (e.g. toggle a counter in model)?
   Runtime is more ergonomic, user-side is simpler.
7. Should `Keyframes` be part of `Stylesheet` only, or also embeddable
   inline via a `Cmd` that injects a one-off `<style>` element?
   Stylesheet-only is cleaner. Inline injection is useful for dynamic
   animations generated from model data.
8. Should `tickSpring` use fixed timestep internally (accumulator pattern
   from time-model.md) to prevent instability on large dt? Probably yes
   for stiff springs. Gentle springs tolerate variable dt.
9. Should `Tween` support reverse / yoyo / repeat? Or leave that to
   `sequenceAnim` (compose forward + backward tweens)?
10. How to interrupt a model animation mid-flight? Spring handles this
    naturally (retarget: set new `target`, velocity carries over). Tween
    needs restart or a "current value" capture.
11. Should `Anim/` live under `Css/` or as a sibling? Sibling is better:
    model animations have nothing to do with CSS. They just happen to
    drive `styleBind`. They could equally drive WebGL uniforms.
12. Should `generate-css.js` live in `scripts/` or in `runtime/`?
    `scripts/` -- it's a build tool, not runtime code.
13. Should the shared class name module (`MyApp.Classes`) be enforced
    by convention or by a type-level mechanism? Convention is simpler.
    A `ClassRef` newtype wrapper could prevent raw string classes, but
    adds friction. Start with convention.
14. Should `renderStylesheet` pretty-print (indented) or compact by
    default? Pretty-print. Minification is a post-step or a separate
    `renderMinified` function. Readability matters for debugging.
