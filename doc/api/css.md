# CSS (Typed Stylesheet DSL)

From `Agdelte.Css` (re-exports all submodules except `Stylesheet` and `Animate`).

## Decl & Style

From `Agdelte.Css.Decl`.

```agda
record Decl : Set where
  constructor _∶_
  field prop : String ; val : String

Style : Set
Style = List Decl
```

| Function | Type | Description |
|----------|------|-------------|
| `_∶_` | `String -> String -> Decl` | Raw property-value pair (escape hatch) |
| `_<>_` | `Style -> Style -> Style` | Compose styles (later wins on conflict) |
| `toAttrs` | `Style -> List (Attr Model Msg)` | Convert to reactive node attributes |
| `singleton` | `Decl -> Style` | Wrap single declaration |
| `none` | `Style` | Empty style |

```agda
-- Escape hatch: any CSS property works immediately
myStyle : Style
myStyle = "display" ∶ "flex" ∷ "gap" ∶ "1rem" ∷ []

-- Composition: later overrides earlier
combined : Style
combined = baseStyle <> overrideStyle
```

## Length

From `Agdelte.Css.Length`.

```agda
data Length : Set where
  px   : ℕ -> Length
  rem  : Float -> Length
  em   : Float -> Length
  pct  : Float -> Length
  vh   : Float -> Length
  vw   : Float -> Length
  zero : Length
```

| Function | Type | Description |
|----------|------|-------------|
| `showLength` | `Length -> String` | Render to CSS (`"16px"`, `"1.5rem"`, `"100%"`) |

## Color

From `Agdelte.Css.Color`.

```agda
data Color : Set where
  hex   : String -> Color                       -- "#ff0000"
  rgb   : ℕ -> ℕ -> ℕ -> Color                 -- rgb(255,0,0)
  rgba  : ℕ -> ℕ -> ℕ -> Float -> Color         -- rgba(255,0,0,0.5)
  hsl   : ℕ -> ℕ -> ℕ -> Color                 -- hsl(0,100%,50%)
  named : String -> Color                        -- "red", "transparent"
  var   : String -> Color                        -- var(--primary)
  raw   : String -> Color                        -- escape hatch
```

| Function | Type | Description |
|----------|------|-------------|
| `showColor` | `Color -> String` | Render to CSS color expression |

## Typed Properties

From `Agdelte.Css.Properties`. All return `Decl`.

### Box Model

| Function | Type | Description |
|----------|------|-------------|
| `padding'` | `Length -> Decl` | padding |
| `padding2` | `Length -> Length -> Decl` | padding (vertical horizontal) |
| `padding4` | `Length -> Length -> Length -> Length -> Decl` | padding (top right bottom left) |
| `margin'` | `Length -> Decl` | margin |
| `margin2` | `Length -> Length -> Decl` | margin (vertical horizontal) |
| `margin4` | `Length -> Length -> Length -> Length -> Decl` | margin (top right bottom left) |

### Sizing

| Function | Type | Description |
|----------|------|-------------|
| `width'` | `Length -> Decl` | width |
| `height'` | `Length -> Decl` | height |
| `maxWidth'` | `Length -> Decl` | max-width |
| `maxHeight'` | `Length -> Decl` | max-height |
| `minWidth'` | `Length -> Decl` | min-width |
| `minHeight'` | `Length -> Decl` | min-height |

### Typography & Color

| Function | Type | Description |
|----------|------|-------------|
| `fontSize'` | `Length -> Decl` | font-size |
| `lineHeight'` | `Length -> Decl` | line-height |
| `color'` | `Color -> Decl` | color |
| `background'` | `Color -> Decl` | background |
| `backgroundColor'` | `Color -> Decl` | background-color |
| `borderColor'` | `Color -> Decl` | border-color |

### Spacing & Border

| Function | Type | Description |
|----------|------|-------------|
| `gap'` | `Length -> Decl` | gap |
| `borderRadius'` | `Length -> Decl` | border-radius |

## Layout Helpers

From `Agdelte.Css.Layout`. All return `Style`.

| Function | Type | Description |
|----------|------|-------------|
| `row` | `Style` | `display: flex; flex-direction: row` |
| `col` | `Style` | `display: flex; flex-direction: column` |
| `center` | `Style` | Centers content (justify + align) |
| `spaceBetween` | `Style` | `justify-content: space-between` |
| `wrap` | `Style` | `flex-wrap: wrap` |
| `grid` | `String -> Style` | Grid with template string |
| `stack` | `Length -> Style` | Vertical column with gap |
| `inline` | `Length -> Style` | Horizontal row with gap |

```agda
toolbar : Style
toolbar = row <> center <> "padding" ∶ "0.5rem" ∷ []

sidebar : Style
sidebar = col <> stack (px 16)
```

## CSS Variables

From `Agdelte.Css.Variables`.

| Function | Type | Description |
|----------|------|-------------|
| `cssVar` | `String -> String -> Decl` | Define `--name: value` |
| `varRef` | `String -> String` | Reference `var(--name)` |

```agda
themeVars : Style
themeVars = cssVar "primary" "#4a9eff"
          ∷ cssVar "radius" "8px"
          ∷ []

themedCard : Style
themedCard = color' (var "primary")
           ∷ "border-radius" ∶ varRef "radius"
           ∷ []
```

## Easing & Duration

From `Agdelte.Css.Easing`.

```agda
data Easing : Set where
  ease easeIn easeOut easeInOut linear : Easing
  cubicBezier : Float -> Float -> Float -> Float -> Easing
  raw : String -> Easing

data Duration : Set where
  ms : ℕ -> Duration
  s  : Float -> Duration
```

### Easing Functions (Float -> Float)

For model-driven animations (not CSS transitions):

| Function | Type | Description |
|----------|------|-------------|
| `linearFn` | `Float -> Float` | Identity |
| `easeInFn` | `Float -> Float` | Cubic ease-in (t^3) |
| `easeOutFn` | `Float -> Float` | Cubic ease-out (1-(1-t)^3) |
| `easeInOutFn` | `Float -> Float` | Piecewise cubic |

## Transitions

From `Agdelte.Css.Transition`.

```agda
record TransSpec : Set where
  field
    property : String
    dur      : Duration
    easing   : Easing
    delay    : Duration
```

| Function | Type | Description |
|----------|------|-------------|
| `trans` | `String -> Duration -> Easing -> TransSpec` | No-delay transition spec |
| `transition'` | `List TransSpec -> Decl` | Render to `transition` declaration |

```agda
hoverTransition : Decl
hoverTransition = transition' (
    trans "box-shadow" (ms 200) ease
  ∷ trans "transform" (ms 200) ease
  ∷ [])
```

## Animations

From `Agdelte.Css.Animation`.

```agda
data Stop : Set where
  at   : ℕ -> Stop     -- percentage (at 50 = "50%")
  from : Stop           -- "from" (= 0%)
  to   : Stop           -- "to"   (= 100%)

record Keyframes : Set where
  field name  : String
        stops : List (Stop * Style)

record Animation : Set where
  field animName  : String ; dur : Duration ; easing : Easing
        delay : Duration ; count : IterCount
        direction : Direction ; fillMode : FillMode
```

| Function | Type | Description |
|----------|------|-------------|
| `anim` | `String -> Duration -> Animation` | Defaults: no delay, 1x, no fill |
| `keyframeRule` | `Keyframes -> Rule` | Convert to Stylesheet rule |
| `animation'` | `Animation -> Decl` | Single animation declaration |
| `animations` | `List Animation -> Decl` | Multiple animations |
| `staggerDelay` | `ℕ -> ℕ -> Decl` | `animation-delay` for staggered items |

### Preset Keyframes

From `Agdelte.Css.Animate` (import separately).

**Entrances:** `fadeIn`, `fadeInUp`, `fadeInDown`, `fadeInLeft`, `fadeInRight`, `slideInUp`, `slideInDown`, `slideInLeft`, `slideInRight`, `scaleIn`, `zoomIn`

**Exits:** `fadeOut`, `fadeOutUp`, `fadeOutDown`, `slideOutUp`, `slideOutDown`, `scaleOut`, `zoomOut`

**Attention:** `pulse`, `bounce`, `shake`, `wobble`, `flash`

**Loop:** `spin`

```agda
open import Agdelte.Css.Animate

appCSS : Stylesheet
appCSS = keyframeRule fadeIn
       ∷ rule ".panel-enter" (animation' (anim "fadeIn" (ms 300)) ∷ [])
       ∷ []
```

## Conditional Styles

From `Agdelte.Css.Conditional`.

| Function | Type | Description |
|----------|------|-------------|
| `styleIf` | `Bool -> Style -> Style` | Include style if true, else empty |
| `styleWhen` | `Bool -> Style -> Style -> Style` | Choose between two styles |

## Stylesheet (Static CSS Generation)

From `Agdelte.Css.Stylesheet` (import separately).

```agda
data Rule : Set where
  rule    : String -> Style -> Rule            -- selector { ... }
  media   : String -> List Rule -> Rule        -- @media (...) { ... }
  keyframe : String -> List (String * Style) -> Rule  -- @keyframes name { ... }
  rawRule : String -> Rule                     -- raw CSS text

Stylesheet : Set
Stylesheet = List Rule
```

| Function | Type | Description |
|----------|------|-------------|
| `renderRule` | `Rule -> String` | Single rule to CSS text |
| `renderStylesheet` | `Stylesheet -> String` | Full stylesheet to CSS text |

```agda
appCSS : Stylesheet
appCSS =
    rule ".card" (padding' (px 16) ∷ borderRadius' (px 8) ∷ [])
  ∷ rule ".card:hover" ("box-shadow" ∶ "0 8px 24px rgba(0,0,0,0.3)" ∷ [])
  ∷ media "(max-width: 768px)" (
      rule ".card" (padding' (px 8) ∷ []) ∷ [])
  ∷ keyframeRule fadeIn
  ∷ []
```

## Build Pipeline

Agda compiles the `Stylesheet` value to JavaScript. A Node.js script extracts the CSS:

```bash
# 1. Compile Agda to JS
npm run build:css-demo

# 2. Generate CSS file from compiled module
node scripts/generate-css.js jAgda.CssDemo appCSS examples_html/generated/css-demo.css

# 3. Link in HTML
# <link rel="stylesheet" href="generated/css-demo.css">
```

The `generate-css.js` script:
1. Imports the compiled Agda module (`_build/jAgda.*.mjs`)
2. Imports `renderStylesheet` from `jAgda.Agdelte.Css.Stylesheet`
3. Calls `renderStylesheet(stylesheet)` to produce CSS text
4. Writes to output file

Optional `--hash` flag appends an 8-char MD5 hash to the filename for cache busting.

npm scripts:

```bash
npm run css:demo        # CssDemo -> css-demo.css
npm run css:full-demo   # CssFullDemo -> css-full-demo.css
npm run css:all         # All CSS + anim data
```

## Module Hierarchy

```
Agdelte.Css                  -- re-exports all below (except Stylesheet, Animate)
  Agdelte.Css.Decl           -- Decl, Style, _<>_, toAttrs
  Agdelte.Css.Show           -- showFloat (CSS-safe)
  Agdelte.Css.Length          -- Length (px, rem, em, pct, vh, vw, zero)
  Agdelte.Css.Color           -- Color (hex, rgb, rgba, hsl, named, var, raw)
  Agdelte.Css.Properties      -- Typed property constructors
  Agdelte.Css.Layout           -- row, col, center, stack, inline, grid
  Agdelte.Css.Variables        -- cssVar, varRef
  Agdelte.Css.Easing           -- Easing, Duration, easing functions
  Agdelte.Css.Transition       -- TransSpec, transition'
  Agdelte.Css.Animation        -- Keyframes, Animation, keyframeRule
  Agdelte.Css.Conditional      -- styleIf, styleWhen

Agdelte.Css.Animate          -- SEPARATE: preset keyframes (fadeIn, slideIn, etc.)
Agdelte.Css.Stylesheet       -- SEPARATE: Rule, Stylesheet, renderStylesheet
```
