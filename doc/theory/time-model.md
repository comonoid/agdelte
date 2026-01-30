# Time Model

> Reference. For conceptual understanding: [README.md](../README.md)
>
> **Status:** `interval` and `animationFrame` are implemented in MVP. Fixed timestep is a usage pattern, not built-in functionality.

## Core Principle: Everything is Discrete

**Agdelte has no continuous time.** The entire system is built on discrete events.

```
Event ───► Event ───► Event ───► Event
  │          │          │          │
  ▼          ▼          ▼          ▼
Tick 0    Tick 1    Tick 2    Tick 3
```

- **Signal** — discrete stream of values (one value per tick)
- **Event** — discrete events (list of events per tick)
- **animationFrame** — discrete Event, fires every frame
- **interval** — discrete Event, fires every N ms

No functions `Time → A`. No "continuous Behavior". Only discrete events.

---

## Tick

**Tick** — atomic unit of time. One tick = one event loop iteration.

```
External world          Runtime              Application
     │                    │                       │
     │  event             │                       │
     ├───────────────────►│                       │
     │                    │  update(msg, model)   │
     │                    ├──────────────────────►│
     │                    │                       │
     │                    │  newModel             │
     │                    │◄──────────────────────┤
     │                    │                       │
     │                    │  render(view)         │
     │                    ├───────────────────────►
     │                    │                       │
     │                    │  idle...              │
```

Tick boundaries:
- Each external event (click, timer, HTTP response) — one tick
- Per tick: event → update → update subscriptions → render
- Between ticks — system is idle

---

## Why Not Continuous Time?

Classic FRP (Conal Elliott):
```haskell
type Behavior a = Time → a  -- Time ∈ ℝ (continuous)
```

**Problems:**

| Problem | Description |
|---------|-------------|
| Non-computable | Computer is discrete — ℝ is not representable |
| Time leaks | Behavior may require entire history |
| Undefined | When to compute? 60 FPS? 120 FPS? |
| Thunk accumulation | Laziness → memory leaks |

**Agdelte's solution:** reject the illusion of continuity.

```
Classic FRP:                 Agdelte:

  Behavior a = Time → a        Signal a = now + next
  "value at EVERY moment"      "value at EVERY TICK"

  Reality: sampled at          Reality: exactly how
  discrete moments             we compute it
```

---

## animationFrame — Discrete Event

`animationFrame` is a **regular Event** that fires every browser frame.

```agda
animationFrame : Event FrameInfo

record FrameInfo : Set where
  field
    dt  : ℕ    -- milliseconds since last event (measurement!)
    fps : ℕ    -- current FPS (measurement!)
```

**Key understanding:**
- `animationFrame` is **not** a "continuous source"
- These are discrete events, ~60 times per second
- `dt` — not "continuous time", but measurement of interval between events
- `fps` — measured event frequency

```agda
events m =
  if m.animating
  then mapE Tick animationFrame  -- subscribe to discrete events
  else never                      -- no events, browser idle
```

When `animating = false`, no events occur. System is idle. Battery is saved.

---

## Animations: Interpolation Between Discrete Events

For smooth animations, use `dt` for interpolation:

```agda
update (Tick frame) m = record m
  { position = m.position + m.velocity * frame.dt / 1000 }
```

This is **not** continuous movement. It's:
1. Received discrete event with `dt = 16`
2. Computed new position: `position += velocity * 0.016`
3. Rendered
4. Waiting for next discrete event

**Visually** looks smooth (60 FPS is enough for the eye). **Technically** — discrete steps.

---

## Fixed Timestep — Pattern for Physics

Variable dt problem:

```
Event 1: dt = 16ms  → position += velocity * 0.016
Event 2: dt = 100ms → position += velocity * 0.100  // lag!
                      ↑
            Object "flies through" wall
```

**Solution:** fixed physics step (like in game engines).

```agda
-- This is a usage pattern, not a primitive!

FIXED_DT : ℕ
FIXED_DT = 16  -- 60 Hz

record PhysicsModel (A : Set) : Set where
  field
    current     : A      -- current physics state
    previous    : A      -- for render interpolation
    accumulator : ℕ      -- accumulated time

updatePhysics : (A → A) → ℕ → PhysicsModel A → PhysicsModel A
updatePhysics step dt model = go (record model { accumulator = model.accumulator + dt })
  where
    go m = if m.accumulator >= FIXED_DT
           then go (record m
             { current = step m.current
             ; previous = m.current
             ; accumulator = m.accumulator - FIXED_DT
             })
           else m
```

**How it works:**

```
animationFrame gives dt = 100ms (lag!)

accumulator += 100  -- now 100

while accumulator >= 16:
  step()            -- physics with fixed dt=16
  accumulator -= 16

-- Executed 6 physics steps
-- accumulator = 4 (remainder for render interpolation)
```

Physics is always deterministic. Same input → same result.

---

## Render Interpolation

After physics, `accumulator` contains time "remainder". Use for smooth rendering:

```agda
interpolate : Lerp A → PhysicsModel A → A
interpolate lerp m =
  let alpha = m.accumulator * 1000 / FIXED_DT  -- 0..1000
  in lerp m.previous m.current alpha

Lerp : Set → Set
Lerp A = A → A → ℕ → A  -- from → to → alpha → result
```

```
previous ●────────────────● current
              ↑
         alpha = 0.25
              ↓
           render here
```

---

## Example: Bouncing Ball

```agda
record Ball : Set where
  y  : ℤ    -- position (millimeters)
  vy : ℤ    -- velocity (mm/s)

GRAVITY : ℤ
GRAVITY = -9800  -- mm/s²

ballStep : Ball → Ball
ballStep b =
  let newVy = b.vy + GRAVITY * FIXED_DT / 1000
      newY  = b.y + newVy * FIXED_DT / 1000
  in if newY < 0
     then record { y = 0; vy = negate newVy * 80 / 100 }  -- bounce
     else record { y = newY; vy = newVy }

-- In update:
update (Tick frame) m = record m
  { physics = updatePhysics ballStep frame.dt m.physics }

-- In view:
view m =
  let ball = interpolate lerpBall m.physics
  in div [ style [("transform", "translateY(" ++ show ball.y ++ "mm)")] ]
       [ text "●" ]
```

---

## Comparison with Other Systems

| System | Time Model | Comment |
|--------|------------|---------|
| Fran (Conal Elliott) | Continuous (Time → A) | Beautiful mathematically, problematic in practice |
| Yampa | Discrete (Signal Functions) | No time leaks |
| Reflex | Discrete | Spider timeline |
| Elm | Discrete | Ticks on events |
| Game engines | Discrete + fixed timestep | Industry standard |
| **Agdelte** | **Discrete** | Event + fixed timestep pattern |

---

## Summary

```
┌─────────────────────────────────────────────────────────────┐
│  BASIS: discrete events (Event)                              │
│                                                              │
│  interval 1000      → Event ⊤     (every second)            │
│  animationFrame     → Event FrameInfo (every frame)         │
│  keyboard           → Event Key   (on keypress)             │
│  request            → Event Response (on response)          │
│                                                              │
│  Everything — discrete events. No continuity.               │
├──────────────────────────────────────────────────────────────┤
│  PATTERN: fixed timestep (for physics)                       │
│                                                              │
│  • Accumulate dt from animationFrame                         │
│  • Execute physics steps with fixed FIXED_DT                 │
│  • Interpolate render                                        │
│                                                              │
│  Determinism, replay, network synchronization.              │
├──────────────────────────────────────────────────────────────┤
│  "CONTINUITY": an illusion                                   │
│                                                              │
│  • 60 events/sec is visually indistinguishable from         │
│    continuity                                                │
│  • dt allows interpolation between events                    │
│  • Technically — discrete steps                              │
│                                                              │
│  This is honest. And it works.                              │
└──────────────────────────────────────────────────────────────┘
```

**Philosophy:** continuous time is a useful abstraction for mathematics, but an illusion for implementation. We don't pretend. Everything is discrete.
