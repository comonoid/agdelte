# Agdelte

**Reactive UI framework with dependent types.**

Svelte 5 introduced Runes — explicit reactivity instead of compiler magic. A step in the right direction, but TypeScript doesn't truly understand Runes; it's just an overlay.

Agdelte brings the same ideas to a language with a real type system. Reactivity through standard abstractions: Functor, Applicative, streams. Effects are explicit in types. Impossible states are unrepresentable.

## Core Idea

Agdelte combines **Elm Architecture** with **declarative subscriptions** and **explicit commands**:

```agda
record App (Model Msg : Set) : Set where
  field
    init    : Model                    -- initial state
    update  : Msg → Model → Model      -- pure state transition (simple!)
    view    : Model → Html Msg         -- pure rendering
    subs    : Model → Event Msg        -- subscriptions (continuous)
    command : Msg → Model → Cmd Msg    -- commands (HTTP, etc.)
```

Key insight: **separation of concerns**:
- `Event` (subs) — subscriptions to continuous sources (timers, keyboard)
- `Cmd` (command) — commands (HTTP requests)
- `Task` — monadic chains with do-notation (sequential HTTP)
- `update` — stays simple: `Msg → Model → Model`

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
data Msg = Inc | Dec | Fetch | GotData String | GotError String

data Status = Idle | Loading | Ready String

record Model : Set where
  field
    count  : ℕ
    status : Status

-- update stays simple!
update : Msg → Model → Model
update Inc m = record m { count = suc (m .count) }
update Dec m = record m { count = pred (m .count) }
update Fetch m = record m { status = Loading }
update (GotData d) m = record m { status = Ready d }
update (GotError _) m = record m { status = Idle }

-- command: when to make HTTP requests
command : Msg → Model → Cmd Msg
command Fetch _ = httpGet "/api/data" GotData GotError
command _ _ = ε  -- no command for other messages

-- subs: continuous subscriptions (none here)
subs : Model → Event Msg
subs _ = never

app : App Model Msg
app = mkCmdApp
  (record { count = 0; status = Idle })
  update
  (λ m → div []
      [ button [ onClick Dec ] [ text "-" ]
      , span [] [ text (show (m .count)) ]
      , button [ onClick Inc ] [ text "+" ]
      , button [ onClick Fetch ] [ text "Load" ]
      ])
  subs
  command
```

**Key insight:**
- HTTP requests go in `command`, executed **once** when Fetch is dispatched
- `subs` is for **continuous** subscriptions (timers, keyboard)
- `update` stays **simple**: `Msg → Model → Model`

### Task for HTTP Chains

For sequential HTTP requests, use `Task` with do-notation:

```agda
-- Chain of requests with do-notation
fetchChain : Task String
fetchChain = do
  user ← http "/api/user"
  posts ← http ("/api/users/" ++ user ++ "/posts")
  comments ← http ("/api/posts/" ++ posts ++ "/comments")
  pure (combine user posts comments)

-- Use in command via attempt
command Fetch _ = attempt fetchChain GotResult
command _ _ = ε
```

`Task` is a monad — compose with `>>=` or do-notation, run via `attempt`.

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
│  mkApp { init, update, view, subs }      -- simple apps    │
│  mkCmdApp { ..., command }               -- with HTTP      │
├─────────────────────────────────────────────────────────────┤
│  Core          │  Event (subs), Cmd (commands), Task (chains)│
├─────────────────────────────────────────────────────────────┤
│  Primitives    │  interval, keyboard (Event)                │
│                │  httpGet, httpPost (Cmd)                   │
│                │  http, attempt (Task → Cmd)                │
├─────────────────────────────────────────────────────────────┤
│  App           │  init, update, view, subs, command         │
├─────────────────────────────────────────────────────────────┤
│  Html          │  Typed elements and attributes             │
├─────────────────────────────────────────────────────────────┤
│  Runtime       │  Event loop, subscriptions, commands       │
├─────────────────────────────────────────────────────────────┤
│  Theory/       │  Poly, Coalg, Lens (isolated, optional)    │
└─────────────────────────────────────────────────────────────┘
```

### App Structure

```agda
record App (Model Msg : Set) : Set where
  field
    init    : Model                    -- initial state
    update  : Msg → Model → Model      -- pure state transition (simple!)
    view    : Model → Html Msg         -- pure rendering
    subs    : Model → Event Msg        -- subscriptions (continuous)
    command : Msg → Model → Cmd Msg    -- commands (HTTP, etc.)
```

- **init** — initial state
- **update** — pure function, stays simple: `Msg → Model → Model`
- **view** — pure function, returns typed Html
- **subs** — subscriptions to continuous events (timers, keyboard)
- **command** — commands (HTTP requests)

DOM events from `view` are handled automatically by runtime.

**Two constructors:**
- `mkApp` — for simple apps (Counter, Timer, Keyboard) — no commands
- `mkCmdApp` — for apps with HTTP — adds command field

## Documentation

| Document | Description |
|----------|-------------|
| [doc/](doc/) | Main documentation |
| [doc/architecture.md](doc/architecture.md) | Core architecture and design |
| [doc/api.md](doc/api.md) | API reference (Event, Cmd, Task, App, Html) |
| [doc/runtime.md](doc/runtime.md) | JavaScript runtime implementation |
| [doc/examples.md](doc/examples.md) | Guide to all examples |

### Additional Notes

| Document | Description |
|----------|-------------|
| [architecture/combinators.md](architecture/combinators.md) | All combinators with types |
| [architecture/time-model.md](architecture/time-model.md) | Time model: ticks, dt |
| [architecture/ffi.md](architecture/ffi.md) | JavaScript FFI reference |
| [architecture/concurrency.md](architecture/concurrency.md) | Phase 3 concurrency (planned) |
| [architecture/vs-svelte.md](architecture/vs-svelte.md) | Comparison with Svelte 5 |
| [architecture/vs-vue3.md](architecture/vs-vue3.md) | Comparison with Vue 3 |

## Project Structure

```
src/
  Agdelte/
    ├── Core/                    -- Простые определения (для пользователя)
    │   ├── Signal.agda          -- Coinductive stream
    │   ├── Event.agda           -- Event — подписки (interval, keyboard)
    │   ├── Cmd.agda             -- Cmd — команды (httpGet, httpPost)
    │   └── Task.agda            -- Task — монадические цепочки (do-notation)
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
    KeyboardDemo.agda            -- Keyboard events
    HttpDemo.agda                -- HTTP via Cmd
    TaskDemo.agda                -- HTTP chains via Task (do-notation)

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

**Phase 2: Extensions** ✅ — separate concepts requiring dedicated learning

- ✅ websocket (wsConnect, wsSend)
- ✅ localStorage (getItem, setItem, removeItem)
- ✅ routing (onUrlChange, pushUrl, replaceUrl, back, forward)
- ✅ Combinators: filterE, merge, debounce, throttle
- ✅ DOM effects: focus, blur, scrollTo, scrollIntoView
- ✅ Clipboard: readClipboard, writeClipboard
- ✅ App composition: _∥_, _⊕ᵃ_, mapMsg, mapModel

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
