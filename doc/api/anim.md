# Anim (Model-Driven Animations)

From `Agdelte.Anim.Tween` and `Agdelte.Anim.Spring`.

Model-driven animations are computed in the Agda model (pure functions), not via CSS.
Values drive `styleBind` each frame. The compiler can evaluate them at compile time
for verification (see [AnimDemo example](../guide/examples.md#anim-demo)).

## Tween

From `Agdelte.Anim.Tween`.

```agda
record Tween (A : Set) : Set where
  field
    elapsed  : ℕ              -- ms elapsed
    duration : ℕ              -- total ms
    from     : A              -- start value
    to       : A              -- end value
    easing   : Float -> Float -- [0,1] -> [0,1]
    lerp     : A -> A -> Float -> A  -- interpolation
```

| Function | Type | Description |
|----------|------|-------------|
| `tickTween` | `Tween A -> ℕ -> Tween A * A` | Advance by dt ms, return (updated tween, current value) |
| `isComplete` | `Tween A -> Bool` | Is elapsed >= duration? |
| `currentValue` | `Tween A -> A` | Interpolated value without advancing time |
| `retargetTween` | `A -> Tween A -> Tween A` | Snapshot current value as new `from`, reset elapsed, set new target |
| `floatLerp` | `Float -> Float -> Float -> Float` | `a + (b - a) * t` |

### Usage

```agda
open import Agdelte.Anim.Tween
open import Agdelte.Css.Easing (easeOutFn)

-- Opacity fade: 0 -> 1 over 300ms with easeOut
opacityTween : Tween Float
opacityTween = record
  { elapsed = 0 ; duration = 300
  ; from = 0.0 ; to = 1.0
  ; easing = easeOutFn ; lerp = floatLerp }

-- Advance 150ms
mid : Tween Float * Float
mid = tickTween opacityTween 150
-- proj₂ mid ≈ 0.875 (easeOut is front-loaded)

-- Retarget mid-flight to 0.5
retargeted : Tween Float
retargeted = retargetTween 0.5 (proj₁ mid)
-- from = 0.875 (snapshot), to = 0.5, elapsed = 0
```

### In a ReactiveApp

```agda
-- Model stores tween state
record Model : Set where
  field opacity : Tween Float

-- On each frame, advance tween
updateModel Tick m =
  let (tw , val) = tickTween (opacity m) 16  -- 16ms per frame
  in record m { opacity = tw }

-- Bind current value to style
styleBind "opacity" (λ m → showFloat (currentValue (opacity m)))
```

## Spring

From `Agdelte.Anim.Spring`.

```agda
record Spring : Set where
  field
    position  : Float    -- current position
    velocity  : Float    -- current velocity
    target    : Float    -- destination
    stiffness : Float    -- spring constant (higher = snappier)
    damping   : Float    -- friction (higher = less bounce)
```

| Function | Type | Description |
|----------|------|-------------|
| `tickSpring` | `Spring -> ℕ -> Spring` | Euler step by dt ms |
| `tickSpringStable` | `Spring -> ℕ -> Spring` | Subdivides into 4ms steps for stability |
| `isSettled` | `Spring -> Bool` | Position within 0.01 of target AND velocity < 0.01 |
| `retarget` | `Float -> Spring -> Spring` | New target, velocity carries over (smooth interrupt) |

### Presets

All presets: `Float -> Float -> Spring` (from -> target).

| Preset | Stiffness | Damping | Character |
|--------|-----------|---------|-----------|
| `gentle` | 120 | 14 | iOS-like smooth motion |
| `snappy` | 400 | 28 | Quick, minimal overshoot |
| `bouncy` | 180 | 8 | Playful bounce |

```agda
-- Dialog slides from 0 to 1
dialogSpring : Spring
dialogSpring = gentle 0.0 1.0

-- After 1 frame (16ms)
frame1 : Spring
frame1 = tickSpringStable dialogSpring 16
-- position ≈ 0.031, moving toward 1.0

-- After ~1.3s (80 frames): settled
settled : Bool
settled = isSettled (iterate 80 (λ s → tickSpringStable s 16) dialogSpring)
-- true

-- Interrupt mid-flight with new target
retargeted : Spring
retargeted = retarget 2.0 frame1
-- target = 2.0, velocity preserved (smooth transition)
```

### In a ReactiveApp

```agda
record Model : Set where
  field dialogY : Spring

updateModel Tick m =
  record m { dialogY = tickSpringStable (dialogY m) 16 }

updateModel Open m =
  record m { dialogY = retarget 1.0 (dialogY m) }

updateModel Close m =
  record m { dialogY = retarget 0.0 (dialogY m) }

-- Bind to transform
styleBind "transform"
  (λ m → "translateY(" ++ showFloat (position (dialogY m) * 100.0) ++ "%)")
```

## Tween vs Spring

| | Tween | Spring |
|---|-------|--------|
| Duration | Fixed (e.g. 300ms) | Open-ended (settles naturally) |
| Easing | Explicit function | Emergent from physics |
| Retarget | Resets elapsed, snaps `from` | Velocity carries over (smooth) |
| Best for | Known duration (fade, slide) | Interactive (drag, snap, dialog) |
| Completion | `isComplete` (elapsed >= duration) | `isSettled` (position + velocity threshold) |

## Compile-Time Verification

Since Tween and Spring are pure functions, Agda evaluates them at compile time:

```agda
-- Verified at compile time:
_ : isComplete (proj₁ (tickTween opacityTween 300)) ≡ true
_ = refl

_ : isSettled (iterateSpring 80 dialogSpring) ≡ true
_ = refl
```

The `AnimDemo.agda` example exports computed values. The build pipeline extracts them to JSON for browser-based verification:

```bash
npm run build:anim-demo                # Agda -> JS
npm run css:anim-data                  # Extract values to JSON
# -> examples_html/generated/anim-demo.json
```

## Module Hierarchy

```
Agdelte.Anim.Tween    -- Tween, tickTween, currentValue, retargetTween, floatLerp
Agdelte.Anim.Spring   -- Spring, tickSpring, tickSpringStable, isSettled, retarget
                       -- Presets: gentle, snappy, bouncy
```

Easing functions shared with CSS: `Agdelte.Css.Easing` exports `linearFn`, `easeInFn`, `easeOutFn`, `easeInOutFn` for use as `Tween.easing`.
