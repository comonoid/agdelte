# Agdelte

**Reactive UI framework with dependent types. No Virtual DOM.**

Svelte showed the way: compile-time reactivity beats runtime diffing. But Svelte's compiler magic is opaque — TypeScript doesn't truly understand it.

Agdelte brings Svelte's key insight to a language with a real type system:
- **Direct DOM updates** via reactive bindings (no Virtual DOM diffing)
- **Declarative templates** with `bind` points that auto-update
- **Static verification** of initial structure + dynamic flexibility via lenses

## Core Idea

Agdelte uses **reactive bindings** — like Svelte, but with dependent types:

```agda
-- Reactive template with bindings (like Svelte)
counterTemplate : Node Model Msg
counterTemplate =
  div [ class "counter" ]
    ( button [ onClick Dec ] [ text "-" ]
    ∷ span [ class "count" ] [ bindF show ]   -- auto-updates on model change!
    ∷ button [ onClick Inc ] [ text "+" ]
    ∷ [] )

-- App with reactive template
record ReactiveApp (Model Msg : Set) : Set₁ where
  field
    init     : Model
    update   : Msg → Model → Model
    template : Node Model Msg    -- NOT a function! Structure with bindings
```

Key insight: **reactive bindings instead of Virtual DOM**:
- `bind` points track which DOM nodes depend on model
- When model changes, only affected bindings update
- No tree diffing, no re-rendering — direct DOM mutations

```agda
-- Binding: reactive connection from Model to DOM
record Binding (Model : Set) (A : Set) : Set where
  field
    extract : Model → A           -- get value from model
    equals  : A → A → Bool        -- detect changes
```

### How It Works (Svelte-style)

```
1. FIRST RENDER:
   - Walk the Node tree, create real DOM
   - For each `bind`, remember (DOMNode, Binding)

2. ON MODEL CHANGE:
   - For each binding: extract(oldModel) vs extract(newModel)
   - If changed: update that DOM node directly
   - NO tree diffing! Direct updates to tracked nodes.
```

This is exactly what Svelte does at compile time, but we do it with explicit bindings that the type system can verify.

### Theoretical Foundation

The `Theory/` module (isolated, optional) establishes correspondence with **Polynomial Functors** (Spivak, Niu):

- Reactive bindings as lens-like structures
- Widget networks as polynomial machines
- Composition via polynomial operations (⊗, ⊕)

**Multi-level architecture:**
```
Level 3: Declarative DSL    — button [ onClick Dec ] [ bindF show ]
Level 2: Lenses             — navigation, modification, composition
Level 1: Polynomials        — mathematical foundation
```

## Quick Example

```agda
-- Reactive Counter (like Svelte)
module ReactiveCounter where

open import Agdelte.Reactive.Node

-- Model & Messages
Model = ℕ

data Msg : Set where
  Inc Dec : Msg

-- Pure update
update : Msg → Model → Model
update Inc n = suc n
update Dec zero = zero
update Dec (suc n) = n

-- Declarative template with reactive binding
template : Node Model Msg
template =
  div [ class "counter" ]
    ( button [ onClick Dec ] [ text "-" ]
    ∷ span [ class "count" ] [ bindF show ]   -- bindF show = auto-update!
    ∷ button [ onClick Inc ] [ text "+" ]
    ∷ [] )

-- App
app : ReactiveApp Model Msg
app = mkReactiveApp 0 update template
```

**Compare to Svelte:**
```svelte
<script>
  let count = 0;
</script>

<div class="counter">
  <button on:click={() => count--}>-</button>
  <span class="count">{count}</span>
  <button on:click={() => count++}>+</button>
</div>
```

Same declarative style, but with dependent types and no compiler magic.

## Why Agdelte?

| | Svelte 5 | Virtual DOM (React/Elm) | Agdelte |
|--|----------|-------------------------|---------|
| DOM updates | Direct (compiled) | Diff tree, patch | Direct (bindings) |
| Performance | Fast | Overhead from diffing | Fast |
| Reactivity | Compiler magic | Runtime diffing | Explicit bindings |
| Type safety | TypeScript | Varies | Dependent types |
| Impossible states | Runtime | Runtime | Compile-time |

**Key advantage over Virtual DOM**: No tree reconstruction, no diffing algorithm. When model changes, only the bound DOM nodes update — exactly like Svelte.

## Architecture

```
┌─────────────────────────────────────────────────────────────┐
│  Level 3: Declarative DSL                                   │
│  button [ onClick Dec ] [ bindF show ]                     │
│  Aesthetic, readable, statically verified                   │
├─────────────────────────────────────────────────────────────┤
│  Level 2: Lenses                                            │
│  Navigation, modification, composition                      │
│  Dynamic flexibility at runtime                             │
├─────────────────────────────────────────────────────────────┤
│  Level 1: Polynomials                                       │
│  Mathematical foundation (Spivak, Niu)                      │
└─────────────────────────────────────────────────────────────┘
```

### ReactiveApp Structure

```agda
record ReactiveApp (Model Msg : Set) : Set₁ where
  field
    init     : Model                    -- initial state
    update   : Msg → Model → Model      -- pure state transition
    template : Node Model Msg           -- reactive template (NOT a function!)
```

- **init** — initial state
- **update** — pure function: `Msg → Model → Model`
- **template** — declarative structure with bindings (like Svelte template)

### Node — Reactive Template

```agda
data Node (Model Msg : Set) : Set₁ where
  text : String → Node Model Msg                           -- static text
  bind : Binding Model String → Node Model Msg             -- reactive binding!
  elem : String → List (Attr Model Msg) → List (Node Model Msg) → Node Model Msg
```

The key difference from Virtual DOM: `template` is **data**, not a function. Bindings track exactly which DOM nodes need updating.

## Documentation

| Document | Description |
|----------|-------------|
| [doc/](doc/) | Main documentation |
| [doc/architecture.md](doc/architecture.md) | Core architecture and design |
| [doc/api.md](doc/api.md) | API reference (Node, Event, Cmd, Task, Optic) |
| [doc/runtime.md](doc/runtime.md) | JavaScript runtime implementation |
| [doc/examples.md](doc/examples.md) | Guide to all examples |

### Additional Documents

| Document | Description |
|----------|-------------|
| [doc/combinators.md](doc/combinators.md) | All combinators with types |
| [doc/time-model.md](doc/time-model.md) | Time model: ticks, dt |
| [doc/polynomials.md](doc/polynomials.md) | Polynomial functors: theory and phases |
| [doc/vs-svelte.md](doc/vs-svelte.md) | Comparison with Svelte 5 |
| [doc/vs-vue3.md](doc/vs-vue3.md) | Comparison with Vue 3 |
| [doc/research.md](doc/research.md) | Research: wiring diagrams, linear types, session types |

## Project Structure

```
src/
  Agdelte/
    ├── Reactive/                -- Reactive templates (Svelte-style)
    │   ├── Node.agda            -- Node, Binding, ReactiveApp
    │   ├── Lens.agda            -- Lens, fstLens, sndLens
    │   └── Optic.agda           -- Prism, Traversal, Affine, Optic, routeMsg
    │
    ├── Core/                    -- Effects
    │   ├── Signal.agda          -- Coinductive stream
    │   ├── Event.agda           -- Event — subscriptions (interval, keyboard)
    │   ├── Cmd.agda             -- Cmd — commands (httpGet, httpPost)
    │   └── Task.agda            -- Task — monadic chains (do-notation)
    │
    ├── Theory/                  -- Mathematical foundation (optional)
    │   ├── Poly.agda            -- Polynomial functors, Coalg, Lens
    │   └── PolySignal.agda      -- Signal ≅ Coalg (Mono A ⊤)
    │
    └── Test/                    -- Tests
        ├── Interpret.agda       -- Pure event testing (SimEvent)
        └── OpticTest.agda       -- 16 optic proofs

examples/
    Counter.agda                 -- Counter with reactive bindings
    Timer.agda                   -- Stopwatch with interval
    Todo.agda                    -- TodoMVC-style app
    Keyboard.agda            -- Global keyboard events
    Http.agda                -- HTTP requests
    Task.agda                -- Task chains (do-notation)
    WebSocket.agda           -- WebSocket communication
    Router.agda              -- SPA routing
    Composition.agda         -- App composition (zoomNode)
    Transitions.agda         -- CSS enter/leave animations (whenT)
    Combinators.agda         -- Event pipeline (foldE, mapFilterE)
    OpticDynamic.agda        -- Dynamic optics (ixList, Traversal, _∘O_)

runtime/
    reactive.js                  -- Main: runReactiveApp, renderNode, updateBindings
    reactive-auto.js             -- Auto-loader (data-agdelte attribute)
    events.js                    -- Event interpretation, subscribe/unsubscribe
```

## Key Properties

**No Virtual DOM.** Direct DOM updates via reactive bindings — like Svelte, but explicit.

**Purity.** `update` is a pure function. Template is data, not computation.

**Declarativity.** Template describes *structure*, bindings describe *what changes*.

**Performance.** No tree diffing. O(bindings) updates, not O(tree size).

**Composability.** Events and bindings combine with standard operations:

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

Structured concurrency, automatic resource management, no leaks. See [doc/api.md](doc/api.md).

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

**Phase 1: MVP** ✅

- Core: Signal, Event, Cmd, Task
- Primitives: interval, animationFrame, keyboard, mouse, HTTP
- Runtime: event loop

**Phase 2: Reactive Architecture** ✅

- ReactiveApp, Node, Binding — Svelte-style, no Virtual DOM
- All 9 examples migrated (Counter, Timer, Todo, Keyboard, HTTP, Task, WebSocket, Router, Composition)
- Runtime with direct DOM updates via reactive bindings
- zoomNode for component composition

**Phase 3: Incremental Updates** ✅

- Binding scopes — each `when`/`foreach` block gets its own scope; cleanup on destroy
- `foreachKeyed` — key-based list reconciliation (add/remove/reorder without rebuild)
- `whenT` — conditional rendering with CSS enter/leave transitions

**Phase 4: Widget Lenses** ✅

- `Lens Outer Inner` with get/set/modify
- Lens composition `_∘L_`, `fstLens`, `sndLens`
- `zoomNode` — maps both model AND messages for full component composition

**Phase 5: Combinators & Testing** ✅

- Stateful Event constructors: `foldE`, `mapFilterE`, `switchE` (runtime maintains state)
- Derived combinators: `accumE`, `mapAccum`, `gate`
- Pure testing: `Agdelte.Test.Interpret` — `SimEvent`, `simFoldE`, `interpretApp`, propositional equality proofs

**Phase 6: Optics + Widget Networks** ✅

- Optics hierarchy: `Prism`, `Traversal`, `Affine`, unified `Optic` with `_∘O_`
- `zoomNodeL` / `zoomAttrL` — typed component composition via Lens + Prism
- `routeMsg` — automatic message routing via Prism + Lens
- `ixList` — indexed list access as Affine
- 16 propositional equality proofs, Optic example

**Phase 7: Concurrency + Distribution**

- Agents as polynomial coalgebras, channels, structured concurrency
- `ProcessOptic` / `RemoteOptic` — same `Optic` interface across processes and hosts
- Big Optic spans local widgets, processes, and remote hosts uniformly
- See [doc/research.md](doc/research.md)

**Phase 8: Developer Experience**

- DevTools via Big Optic (network inspection across processes/hosts)
- Time-travel debugging
- Hot reload

**Phase 9: Formal properties + Session types**

- `Optic ≅ Poly.Lens` for monomial case — formal connection
- Lens laws proofs
- ReactiveApp ↔ Coalg formal connection

## Philosophy

> Svelte's performance + dependent types = Agdelte

Agdelte takes Svelte's key insight — direct DOM updates without Virtual DOM — and makes it explicit and type-safe.

- **Svelte**: Compiler generates direct DOM updates (magic)
- **Agdelte**: Explicit bindings that the type system verifies (transparent)

Same performance characteristics, but you can see and reason about the reactive connections.

## License

MIT
