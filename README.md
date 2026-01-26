# Agdelte

**Reactive UI framework with dependent types.**

Svelte 5 introduced Runes — explicit reactivity instead of compiler magic. A step in the right direction, but TypeScript doesn't truly understand Runes; it's just an overlay.

Agdelte brings the same ideas to a language with a real type system. Reactivity through standard abstractions: Functor, Applicative, streams. Effects are explicit in types. Impossible states are unrepresentable.

## Core Idea

Everything is a **system implementing an interface**.

```agda
-- Poly: interface (what system outputs, what it accepts)
record Poly : Set₁ where
  field
    Pos : Set              -- positions (outputs)
    Dir : Pos → Set        -- directions (inputs)

-- Sys: system = coalgebra of polynomial
record Sys (P : Poly) : Set₁ where
  field
    State : Set
    pos   : State → P.Pos
    step  : (s : State) → P.Dir (pos s) → State

-- Signal, Event, App — all are Sys P for different P (all discrete!)
Signal A = Sys (A, λ _ → ⊤)           -- discrete stream: one value per tick
Event A  = Signal (List A)            -- discrete events: list per tick
App      = Sys (Html Msg, λ _ → Msg)  -- outputs Html, accepts Msg
```

Theoretical foundation: **Polynomial Functors** (Spivak, Niu).

**All IO is Event.** Timers, HTTP, WebSocket, animations — unified under one mechanism. Everything is discrete events:

```agda
interval       : ℕ → Event ⊤              -- discrete ticks every N ms
animationFrame : Event FrameInfo          -- discrete event per frame (dt for interpolation)
keyboard       : Event Key                -- discrete key presses
request        : Request → Event Response -- discrete HTTP responses
websocket      : Url → WebSocket          -- discrete messages
```

No continuous time. `animationFrame` provides `dt` (milliseconds since last event) for interpolation, but it's still discrete events.

## Quick Example

```agda
-- Counter with HTTP fetch
data Msg = Inc | Dec | Fetch | GotData Response

data Status = Idle | Loading | Ready Data

record Model : Set where
  field
    count  : ℕ
    status : Status

app : App Msg Model
app = record
  { init = { count = 0; status = Idle }

  ; update = λ where
      Inc m → record m { count = suc (m .count) }
      Dec m → record m { count = pred (m .count) }
      Fetch m → record m { status = Loading }
      (GotData (ok _ body)) m → record m { status = Ready (parse body) }
      (GotData (error _ _)) m → record m { status = Idle }

  ; view = λ m → div []
      [ button [ onClick Dec ] [ text "-" ]
      , span [] [ text (show (m .count)) ]
      , button [ onClick Inc ] [ text "+" ]
      , button [ onClick Fetch, disabled (isLoading m) ] [ text "Load" ]
      , viewStatus (m .status)
      ]

  ; events = λ m → case m .status of λ where
      Loading → mapE GotData (request (get "/api/data"))
      _ → never
  }
```

**Key insight:** `events` depends on `Model`. When `status = Loading`, runtime subscribes to the HTTP request. When response arrives and status changes — automatic unsubscribe. No manual cleanup, no resource leaks.

## Why Agdelte?

| | Svelte 5 | Agdelte |
|--|----------|---------|
| Reactivity | Compiler magic (`$state`, `$effect`) | Standard abstractions (Signal, Event) |
| State updates | Mutation | Pure functions (`update : Msg → Model → Model`) |
| Side effects | Hidden in `$effect` | Explicit in types (`events : Model → Event Msg`) |
| Type safety | Optional TypeScript | Dependent types with proofs |
| Impossible states | Runtime errors | Compile-time errors |

## Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                         Agdelte                             │
├─────────────────────────────────────────────────────────────┤
│  Core          │  Signal, Event, combinators                │
├─────────────────────────────────────────────────────────────┤
│  Primitives    │  interval, keyboard, request, websocket    │
├─────────────────────────────────────────────────────────────┤
│  App           │  init, update, view, events                │
├─────────────────────────────────────────────────────────────┤
│  Html          │  Typed elements and attributes             │
├─────────────────────────────────────────────────────────────┤
│  Runtime       │  Event loop, subscriptions, rendering      │
└─────────────────────────────────────────────────────────────┘
```

### App Structure

```agda
record App (Msg : Set) (Model : Set) : Set where
  field
    init   : Model                    -- initial state
    update : Msg → Model → Model      -- pure state transition
    view   : Model → Html Msg         -- pure rendering
    events : Model → Event Msg        -- declarative subscriptions
```

- **init** — initial state
- **update** — pure function, no side effects, easily testable
- **view** — pure function, returns typed Html
- **events** — which external events to listen to (depends on Model)

DOM events from `view` are handled automatically by runtime.

## Documentation

| Document | Description |
|----------|-------------|
| [description.md](description.md) | Concise overview of the core idea |
| [architecture/](architecture/) | Full architecture documentation |

### Architecture

| Document | Description |
|----------|-------------|
| [architecture/README.md](architecture/README.md) | Three-layer architecture (Poly foundation + Elm-like DSL) |
| [architecture/concurrency.md](architecture/concurrency.md) | Concurrency extension (Web Workers) |
| [architecture/vs-svelte.md](architecture/vs-svelte.md) | Detailed comparison with Svelte 5 |
| [architecture/vs-vue3.md](architecture/vs-vue3.md) | Feature comparison with Vue 3 |

### Reference

| Document | Description |
|----------|-------------|
| [architecture/time-model.md](architecture/time-model.md) | Time model: ticks, animationFrame, fixed timestep |
| [architecture/combinators.md](architecture/combinators.md) | All combinators with types and examples |
| [architecture/ffi.md](architecture/ffi.md) | JavaScript FFI implementations |

## Project Structure

```
src/
  Agdelte/
    ├── Core/                    -- Core (required)
    │   ├── Signal.agda          -- Signal, Functor, Applicative
    │   └── Event.agda           -- Event, combinators, foldp
    │
    ├── Primitive/               -- IO primitives
    │   ├── Interval.agda
    │   ├── AnimationFrame.agda  -- browser frames with delta time
    │   ├── Keyboard.agda
    │   ├── Request.agda
    │   └── WebSocket.agda
    │
    ├── Concurrent/              -- Concurrency (optional)
    │   ├── Worker.agda          -- worker : WorkerFn A B → A → Event B
    │   ├── Pool.agda
    │   └── Parallel.agda        -- parallel, race
    │
    ├── App.agda
    └── Html.agda

runtime/
    index.js                     -- runApp, event loop
    primitives.js                -- interval, keyboard, request, websocket
    dom.js                       -- Html rendering, createElement, applyPatches
    diff.js                      -- diffEvents, diffHtml for subscriptions
```

## Key Properties

**Unification.** Timers, HTTP, WebSocket, Workers — all Event. One mechanism.

**Purity.** `update` and `view` are pure functions. Effects only through Event.

**Declarativity.** `events` describes *what* to listen to, not *how* to manage subscriptions.

**Acyclicity.** Signal is a pure stream. Cyclic dependencies impossible by construction.

**Composability.** Events combine with standard operations:

```agda
-- Basic
never     : Event A                           -- nothing
merge     : Event A → Event A → Event A       -- combine streams
mapE      : (A → B) → Event A → Event B       -- transform
filterE   : (A → Bool) → Event A → Event A    -- filter

-- Sampling (Event + Signal interaction)
snapshot  : (A → B → C) → Event A → Signal B → Event C  -- sample Signal
gate      : Event A → Signal Bool → Event A   -- filter by Signal
changes   : Signal A → Event A                -- events when Signal changes

-- Time-based
debounce  : ℕ → Event A → Event A             -- after N ms pause
throttle  : ℕ → Event A → Event A             -- max once per N ms

-- Switching
switchE   : Event A → Event (Event A) → Event A  -- dynamic Event switching

-- Merging
mergeWith : (A → A → A) → Event A → Event A → Event A  -- merge with function
alignWith : (These A B → C) → Event A → Event B → Event C  -- align different types

-- Accumulators
accumE    : A → Event (A → A) → Event A        -- fold to Event
accumB    : A → Event (A → A) → Signal A       -- fold functions to Signal

-- Deferred
pre       : A → Signal A → Signal A            -- delay by one tick

-- Error handling
catchE    : Event (Result E A) → (E → A) → Event A  -- handle errors

-- Testing
interpret : (Event A → Event B) → List (List A) → List (List B)  -- test Event transformations
```

## Concurrency

Heavy computations that block UI? Use workers — same Event pattern:

```agda
-- Worker is just another Event primitive
worker : WorkerFn A B → A → Event B

-- Same declarative model
events m = if m.computing
  then mapE Done (worker heavyComputation m.data)
  else never
-- Event appears → worker starts
-- Event disappears → worker cancelled (automatic cleanup)
```

Structured concurrency, automatic resource management, no leaks. See [architecture/concurrency.md](architecture/concurrency.md).

## Roadmap

**Phase 1: MVP** — all intuitively understandable concepts

Core:
- Signal, Event
- Basic: never, merge, mapE, filterE, occur
- Signal ↔ Event: foldp, stepper, changes
- Sampling: snapshot, attach, tag, gate
- Accumulators: accumE, accumB
- Time: debounce, throttle
- Other: mergeWith, pre, catchE

Primitives:
- interval, animationFrame, keyboard, mouse, request

App, Html (with keyed), Runtime

**Phase 2: Extensions** — separate concepts requiring dedicated learning

- websocket (complex state, reconnection)
- localStorage (persistence)
- routing (URL, history)
- switchE, alignWith (dynamic streams)
- touch, focus management

**Phase 3: Concurrency** — separate module

- worker, parallel, race, channel
- Worker pools, SharedArrayBuffer

**Phase 4: Advanced** — for experts

- Incremental (patches for large collections)
- Indexed types for UI states
- Session types for protocols
- Linear types for resources

## Philosophy

> Reactivity without magic, IO without imperativity, effects explicit in types.

Agdelte is not "Svelte in Agda". It's a different approach: instead of hiding complexity behind compiler magic, we make everything explicit and let the type system ensure correctness.

The cost is more boilerplate. The benefit is confidence: if it compiles, the data flow is correct, resources are managed, impossible states don't exist.

## License

MIT
