# Agdelte Roadmap

## Overview

| Phase | Name | Status | Key Deliverables |
|-------|------|--------|-----------------|
| 1 | MVP | ✅ Done | Signal, Event, Cmd, Task, Runtime |
| 2 | Reactive Architecture | ✅ Done | ReactiveApp, Node, Binding, zoomNode, 9 examples |
| 3 | Incremental Updates | ✅ Done | Binding scopes, foreachKeyed, whenT transitions |
| 4 | Widget Lenses | ✅ Done | Lens get/set, zoomNode (model + msg), fstLens/sndLens |
| 5 | Combinators & Testing | ✅ Done | foldE, mapFilterE, switchE, accumE, mapAccum, interpret |
| 6 | Optics + Widget Networks | ✅ Done | Prism, Traversal, Affine, Optic, routeMsg, zoomNodeL, 16 proofs |
| 7 | Concurrency + Distribution | Planned | Agents, channels, ProcessOptic, RemoteOptic |
| 8 | Developer Experience | Planned | DevTools via Big Optic, time-travel, hot reload |
| 9 | Formal Properties | Planned | Optic ≅ Poly.Lens, lens laws, session types |

---

## Phase 1: MVP ✅

Core type system and runtime: Signal, Event, Cmd, Task.

**Deliverables:**
- `Signal A` — coinductive stream (value over time)
- `Event A` — discrete occurrences (interval, keyboard, HTTP)
- `Cmd Msg` — side effects (HTTP requests, DOM commands)
- `Task E A` — monadic chains with error handling (do-notation)
- Runtime: JavaScript event loop

**Note:** Phase 1 originally included `App` record (Elm-style with `view : Model → Html Msg`). This was replaced by `ReactiveApp` in Phase 2.

**Files:** `src/Agdelte/Core/` (Signal, Event, Cmd, Task)

---

## Phase 2: Reactive Architecture ✅

Svelte-style direct DOM updates. No Virtual DOM.

**Deliverables:**
- `ReactiveApp Model Msg` — application with reactive template (not a view function)
- `Node Model Msg` — template data structure with reactive bindings
- `Binding Model A` — reactive connection: `extract` + `equals`
- `bindF`, `when`, `foreach` — reactive combinators
- `zoomNode` — component composition (model + message remapping)
- All 9 examples using ReactiveApp/Node
- JavaScript runtime with direct DOM mutations via binding tracking

**Key insight:** Template is **data**, not a function. Bindings tell the runtime exactly which DOM nodes to update on model change — no tree diffing needed.

**Files:** `src/Agdelte/Reactive/Node.agda`, `runtime/reactive.js`

---

## Phase 3: Incremental Updates ✅

Efficient list updates and conditional animations.

**Deliverables:**
- **Binding scopes** — each `when`/`foreach` block gets its own scope; destroyed scopes clean up all bindings (fixes stale binding memory leak)
- **`foreachKeyed`** — key-based list reconciliation: same key = reuse DOM node, new key = render, removed key = destroy. No full list rebuild.
- **`whenT`** — conditional rendering with CSS enter/leave transitions via `Transition` record (`enterClass`, `leaveClass`, `duration`)

**Before:** Removing one item from a 100-item list rebuilds all 100 DOM nodes.
**After:** Removing one item removes one DOM node. The rest stay untouched.

**Files:** `runtime/reactive.js` (scopes, reconciliation), `src/Agdelte/Reactive/Node.agda` (foreachKeyed, whenT, Transition)

---

## Phase 4: Widget Lenses ✅

Full lens-based component composition with bidirectional data flow.

**Deliverables:**
- **`Lens Outer Inner`** — practical get/set lens with `modify`
- **`_∘L_`** — lens composition (zoom deeper)
- **`fstLens`, `sndLens`** — product lenses for composed models
- **`zoomNode`** — maps both model AND messages:
  ```agda
  zoomNode : (M → M') → (Msg' → Msg) → Node M' Msg' → Node M Msg
  ```
  This is the key for proper component composition — child components are fully reusable without manual message wrapping or binding duplication.

**Before** (Composition, manual inlining):
```agda
-- 40 lines of duplicated counter template with LeftMsg/RightMsg wrapping
button (onClick (LeftMsg CounterComponent.Dec) ∷ ...) [ text "-" ]
span [ class "count" ] [ bindF leftCountText ]  -- manual helper function
```

**After** (2 lines, clean composition):
```agda
zoomNode proj₁ LeftMsg counterTemplate
zoomNode proj₂ RightMsg counterTemplate
```

**Relation to Theory:** Practical `Lens A B` is equivalent to polynomial `Lens (Mono A A) (Mono B B)`. Formal proof deferred to Phase 9.

**Files:** `src/Agdelte/Reactive/Lens.agda`, `src/Agdelte/Reactive/Node.agda` (zoomNode), `examples/Composition.agda`

---

## Phase 5: Combinators & Testing ✅

Event combinators as AST constructors with runtime support, plus pure testing.

**Deliverables:**

New Event constructors (stateful, runtime maintains internal state):
- `foldE : A → (B → A → A) → Event B → Event A` — accumulate state across events
- `mapFilterE : (B → Maybe A) → Event B → Event A` — map + filter in one step
- `switchE : Event A → Event (Event A) → Event A` — dynamic event source switching

Derived combinators:
- `accumE : A → Event (A → A) → Event A` — apply function events to accumulator
- `mapAccum : (B → S → S × A) → S → Event B → Event A` — map with state
- `gate : (A → Bool) → Event A → Event A` — synonym for filterE

Pure testing framework (`Agdelte.Test.Interpret`):
- `SimEvent A = List (List A)` — list-based event stream (ticks × simultaneous events)
- `simMapE`, `simFilterE`, `simFoldE`, `simAccumE`, `simMerge`, `simMapFilterE`
- `interpretApp : (B → A → A) → A → SimEvent B → List A` — test update logic
- `collectN : ℕ → SimEvent A → SimEvent A`
- 6 propositional equality proofs as built-in tests

**Design decisions:**
- `foldE`, `mapFilterE`, `switchE` required `{-# NO_UNIVERSE_CHECK #-}` and `{-# NO_POSITIVITY_CHECK #-}` on Event data type (quantification over hidden types lifts to Set₁; `Event (Event A)` breaks strict positivity). Acceptable for JS-compiled project.
- `snapshot` not added as separate constructor — in ReactiveApp, `subs : Model → Event Msg` already provides model access via closure, making snapshot implicit.
- `foldp : Event A → Signal B` not added — in ReactiveApp, the model IS the signal, and `update` IS foldp.

**Files:** `src/Agdelte/Core/Event.agda` (constructors + combinators), `src/Agdelte/Test/Interpret.agda` (pure testing), `runtime/events.js` (foldE, mapFilterE, switchE interpreters)

---

## Phase 6: Optics + Widget Networks ✅

Optics hierarchy for navigation, composition, and widget networks.

**Deliverables:**

Optics (concrete types for API contracts):
- `Prism S A` — `match : S → Maybe A`, `build : A → S` (sum navigation)
- `Traversal S A` — `toList : S → List A`, `overAll : (A → A) → S → S` (collection navigation)
- `Affine S A` — `preview : S → Maybe A`, `set : A → S → S` (Lens ∘ Prism)
- `ixList : ℕ → Affine (List A) A` — indexed list access

Unified Optic (for composition and Big Optic):
- `Optic S A` — `peek : S → Maybe A`, `over : (A → A) → S → S`
- `fromLens`, `fromPrism`, `fromTraversal`, `fromAffine` — projections
- `_∘O_` — single composition operator

Widget network:
- `zoomNodeL : Lens M M' → Prism Msg Msg' → Node M' Msg' → Node M Msg` — typed component composition
- `zoomAttrL : Lens M M' → Prism Msg Msg' → Attr M' Msg' → Attr M Msg`
- `routeMsg : Prism Msg Msg' → Lens M M' → (Msg' → M' → M') → Msg → M → M` — automatic message routing

Testing:
- `OpticTest.agda` — 16 propositional equality proofs (Lens, Prism, Affine, Optic, ixList, routeMsg)
- `OpticDynamic.agda` — example: dynamic list with ixList, Traversal, runtime _∘O_

**Design decision:** Concrete types (Lens, Prism, Traversal) for API contracts and guarantees; unified `Optic` for composition. This avoids combinatorial explosion of compose operators while keeping type safety where it matters.

```
Lens (total access)  ──┐
Prism (sum access)   ──┼──→  Optic (unified)  ──→  Big Optic (whole network)
Traversal (collection)─┘         ∘O                    ∘O chain
```

**Files:** `src/Agdelte/Reactive/Optic.agda`, `src/Agdelte/Reactive/Node.agda` (zoomNodeL), `src/Agdelte/Test/OpticTest.agda`, `examples/OpticDynamic.agda`

---

## Phase 7: Concurrency + Distribution

Agents with typed communication; Optic as uniform access across processes and hosts.

**Planned deliverables:**

Concurrency:
- `Agent` as polynomial coalgebra: `S → Σ Pos (Dir → S)`
- Workers as agents
- Channels as polynomial directions (`Dir`)
- `parallel`, `race`, cancellation
- Structured concurrency via wiring diagrams

Distribution:
- `ProcessOptic : Optic NetworkState ProcessState` — navigate to a process (via IPC)
- `RemoteOptic : Optic ClusterState HostState` — navigate to a host (via HTTP)
- Same `Optic` interface: `preview`/`over`, different transport underneath
- Big Optic spans processes and hosts uniformly

**Key insight:** `Optic` is an AST for navigation, like `Event` is an AST for subscriptions. The runtime interprets the transport: local field access, IPC, or HTTP. The navigation structure is the same at every scale.

```
Optic (field access)  →  Optic (process IPC)  →  Optic (remote HTTP)
      same interface: preview / over
```

- Demo: chat system with multiple agents across processes

See [architecture/concurrency.md](../architecture/concurrency.md).

---

## Phase 8: Developer Experience

DevTools powered by Big Optic. Additional DOM effect primitives.

**Planned deliverables:**
- Network inspector — visualize widget/agent topology via Big Optic
- Time-travel debugging — record/replay state transitions
- Hot reload — update code without losing state
- Cross-process inspection via ProcessOptic/RemoteOptic
- DOM effect Cmds: `setTitle`, `setDocumentTitle`, `focus` improvements

**Key idea:** Big Optic provides uniform access to every widget's and agent's state — local or remote — enabling powerful debugging tools with a single abstraction.

---

## Phase 9: Formal Properties + Session Types

Mathematical rigor and formal correspondence.

**Planned deliverables:**
- Lens laws proofs (get-set, set-get, set-set)
- `Optic ≅ Poly.Lens` for monomial case — formal connection between practical optics and polynomial lenses
- `ReactiveApp ↔ Coalg` correspondence
- Dependent polynomial formalization
- Session type DSL — protocols that depend on interaction history
- Demo: multi-step form with typed state transitions
