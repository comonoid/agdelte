# Agdelte

**Reactive UI framework with dependent types.**

Svelte 5 introduced Runes — explicit reactivity instead of compiler magic. A step in the right direction, but TypeScript doesn't truly understand Runes; it's just an overlay.

Agdelte brings the same ideas to a language with a real type system. Reactivity through standard abstractions: Functor, Applicative, streams. Effects are explicit in types. Impossible states are unrepresentable.

## Core Idea

Agdelte combines **Elm Architecture** with **declarative subscriptions**:

```agda
record App (Model Msg : Set) : Set where
  field
    init   : Model                    -- initial state
    update : Msg → Model → Model      -- pure state transition
    view   : Model → Html Msg         -- pure rendering
    events : Model → Event Msg        -- declarative subscriptions
```

Key insight: `events` depends on `Model`. Subscriptions automatically update when model changes. No manual cleanup.

```agda
-- Signal: discrete stream (one value per tick)
Signal A  -- coinductive: now : A, next : Signal A

-- Event: discrete events (list per tick)
Event A = Signal (List A)
```

### Theoretical Foundation

The `Theory/` module (isolated, optional) establishes correspondence with **Polynomial Functors** (Spivak, Niu):

- `Signal A ≅ Coalg (Mono A ⊤)` — signals as coalgebras
- `App ≅ Coalg (AppPoly) + init + events` — apps as systems
- Composition operators correspond to Poly operations (⊗, ⊕)

**Philosophy:** Simple definitions for ergonomics and clear error messages. Theory in separate module for formal guarantees and proofs.

| Phase | User API | Internal | Theory |
|-------|----------|----------|--------|
| **MVP** | Simple definitions | Simple functions | Isolated in Theory/ |
| **Phase 2+** | Same simple API | Poly inside combinators | Guarantees by construction |
| **Phase 3+** | + Wiring diagrams | Poly everywhere | For advanced users |

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
│  USER: Simple definitions, clear error messages             │
│  App { init, update, view, events }                         │
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
├─────────────────────────────────────────────────────────────┤
│  Theory/       │  Poly, Coalg, Lens (isolated, optional)    │
│                │  Phase 2+: used internally for guarantees  │
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
| [examples/README.md](examples/README.md) | Running examples (Counter, Timer, Todo) |
| [architecture/](architecture/) | Full architecture documentation |

### Architecture

| Document | Description |
|----------|-------------|
| [architecture/README.md](architecture/README.md) | Three-layer architecture (Poly foundation + Elm-like DSL) |
| [architecture/concurrency.md](architecture/concurrency.md) | Concurrency extension — Phase 3 (planned) |
| [architecture/vs-svelte.md](architecture/vs-svelte.md) | Detailed comparison with Svelte 5 |
| [architecture/vs-vue3.md](architecture/vs-vue3.md) | Feature comparison with Vue 3 |

### Reference

| Document | Description |
|----------|-------------|
| [architecture/time-model.md](architecture/time-model.md) | Time model: ticks, animationFrame, fixed timestep |
| [architecture/combinators.md](architecture/combinators.md) | All combinators with types and examples |
| [architecture/ffi.md](architecture/ffi.md) | JavaScript FFI implementations (reference) |

## Project Structure

```
src/
  Agdelte/
    ├── Core/                    -- Простые определения (для пользователя)
    │   ├── Signal.agda          -- Coinductive stream
    │   └── Event.agda           -- Event = Signal (List A)
    │
    ├── Theory/                  -- Теоретическое обоснование (опционально)
    │   ├── Poly.agda            -- Polynomial functors, Coalg, Lens
    │   ├── PolySignal.agda      -- Signal ≅ Coalg (Mono A ⊤)
    │   └── PolyApp.agda         -- App ≅ Coalg (AppPoly)
    │
    ├── Html/                    -- Typed HTML
    │   ├── Types.agda           -- Html, Attr types
    │   ├── Elements.agda        -- div, span, button, input, etc.
    │   ├── Attributes.agda      -- className, style, value, etc.
    │   └── Events.agda          -- onClick, onInput, onKey
    │
    ├── Primitive/               -- IO primitives
    │   ├── Interval.agda        -- interval timer
    │   ├── AnimationFrame.agda  -- browser frames with dt/fps
    │   └── ...                  -- keyboard, mouse, request (Phase 2)
    │
    └── App.agda                 -- App record, mkApp

examples/
    Counter.agda                 -- Simple counter
    Timer.agda                   -- Stopwatch with interval
    Todo.agda                    -- TodoMVC-style app

runtime/
    index.js                     -- runApp, event loop
    dom.js                       -- createElement, patch, VDOM diffing
    events.js                    -- Event processing
    primitives.js                -- interval, animationFrame
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

## Quick Start

```bash
# Install dependencies (Agda 2.6.4+, agda-stdlib 2.0+)

# Build all examples
npm run build:all

# Start dev server
npm run dev

# Open http://localhost:8080/
```

See [examples/README.md](examples/README.md) for details.

## Roadmap

**Phase 1: MVP** ✅ — all intuitively understandable concepts

Core: ✅
- Signal, Event, Poly foundation
- Basic combinators: mapE
- App record with init, update, view, events

Primitives: ✅
- interval, animationFrame

Html: ✅
- Elements: div, span, button, input, ul, li, etc.
- Attributes: className, style, value, checked, disabled
- Events: onClick, onInput, onKey

Runtime: ✅
- Event loop, VDOM patching, efficient handler updates

Examples: ✅
- Counter, Timer, Todo

**Phase 2: Extensions** — separate concepts requiring dedicated learning

- websocket (complex state, reconnection)
- localStorage (persistence)
- routing (URL, history)
- keyboard, mouse (global events)
- request (HTTP)
- More combinators: filterE, merge, snapshot, debounce, throttle
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
