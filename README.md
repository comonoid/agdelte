# Agdelte

**Reactive UI framework with dependent types.**

Svelte 5 introduced Runes — explicit reactivity instead of compiler magic. A step in the right direction, but TypeScript doesn't truly understand Runes; it's just an overlay.

Agdelte brings the same ideas to a language with a real type system. Reactivity through standard abstractions: Functor, Applicative, streams. Effects are explicit in types. Impossible states are unrepresentable.

## Core Idea

```agda
-- Signal: values over time (coinductive stream)
record Signal (A : Set) : Set where
  coinductive
  field
    now  : A          -- current value
    next : Signal A   -- continuation

-- Event: occurrences from the outside world
Event A = Signal (List A)
```

**All IO is Event.** Timers, HTTP, WebSocket — unified under one mechanism:

```agda
interval  : ℕ → Event ⊤              -- timer ticks
keyboard  : Event Key                -- key presses
request   : Request → Event Response -- HTTP responses
websocket : Url → WebSocket          -- bidirectional channel (recv + send)
```

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
| [architecture.md](architecture.md) | Complete architecture for MVP implementation |
| [arch-concurrency.md](arch-concurrency.md) | Concurrency extension (Web Workers) |
| [vs-svelte.md](vs-svelte.md) | Detailed comparison with Svelte 5 (10 examples) |

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
never  : Event A                        -- nothing
merge  : Event A → Event A → Event A    -- combine streams
mapE   : (A → B) → Event A → Event B    -- transform
filterE: (A → Bool) → Event A → Event A -- filter
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

Structured concurrency, automatic resource management, no leaks. See [arch-concurrency.md](arch-concurrency.md).

## Roadmap

**Phase 1: MVP**
- Signal, Event, foldp
- Primitives: interval, keyboard, request, websocket
- App (init, update, view, events)
- Html, Runtime

**Phase 2: Extensions**
- mouse, localStorage, routing
- Concurrency: worker, parallel, race
- Focus management, keyed elements

**Phase 3: Advanced Types**
- Indexed types for UI states
- Session types for protocols
- Linear types for resources

## Philosophy

> Reactivity without magic, IO without imperativity, effects explicit in types.

Agdelte is not "Svelte in Agda". It's a different approach: instead of hiding complexity behind compiler magic, we make everything explicit and let the type system ensure correctness.

The cost is more boilerplate. The benefit is confidence: if it compiles, the data flow is correct, resources are managed, impossible states don't exist.

## License

MIT
