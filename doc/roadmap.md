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
| 7 | Concurrency + Distribution | ✅ Done | Agent coalgebra, dual-backend, HTTP+WS server, RemoteAgent, Multi-Agent |
| 8 | Big Lens (network-wide) | Planned | Big Lens across local widgets, server agents, and browser clients |
| 9 | Developer Experience | Planned | DevTools via Big Optic, time-travel, hot reload |
| 10 | Formal Properties | Planned | Optic ≅ Poly.Lens, lens laws, session types |

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

## Phase 7: Concurrency + Distribution ✅

Dual-backend architecture: same Agda source compiles to JS (browser) and Haskell (server).
Agent coalgebra as the uniform process abstraction. HTTP + WebSocket server. Browser ↔ Server communication.

**Deliverables:**

Agent coalgebra:
- `Agent S I O` — polynomial coalgebra: `state : S`, `observe : S → O`, `step : S → I → S`
- Pure Agda, compiles to both JS and Haskell backends
- `stepAgent` returns new agent + output; `mapObserve`, `mapInput` for transformations
- File: `src/Agdelte/Concurrent/Agent.agda`

Browser-side concurrency:
- `worker` Event primitive — runs Agda-compiled JS in a Web Worker, result as discrete event
- Runtime interpreter in `runtime/events.js` — creates Worker, posts script + input, receives result
- File: `examples/Worker.agda`

Haskell HTTP server:
- Raw-socket HTTP server (`hs/Agdelte/Http.hs`) — no warp/wai, just `Network.Socket`
- `src/Agdelte/FFI/Server.agda` — Haskell FFI postulates: IO monad (`_>>=_`, `pure`, `_>>_`), IORef, HTTP listen, AgentDef
- `server/HttpAgent.agda` — single counter agent exposed via GET `/state` and POST `/step`
- Key lesson: all `{-# FOREIGN GHC import #-}` must be at the top of the Agda module (MAlonzo inline ordering)

Multi-Agent + WebSocket:
- `hs/Agdelte/WebSocket.hs` — manual WS framing (SHA1 via crypton, base64-bytestring; no websockets library to avoid missing libz)
- `hs/Agdelte/AgentServer.hs` — multi-agent server: path-based HTTP routing (`/agent/state`, `/agent/step`), STM `TChan` broadcast to all WS clients
- `server/MultiAgent.agda` — counter (Nat, increment) + toggle (Bool, flip) agents
- `wireAgent` helper: bridges pure Agda `Agent S I O` to mutable Haskell `AgentDef` (IORef-based state)
- WS broadcast format: `"agentName:value"` on each step

Browser ↔ Server:
- `examples/RemoteAgent.agda` — browser client using `Cmd` (`agentQuery`/`agentStep!`) to talk to Haskell Agent
- `agentQuery`, `agentStep`, `agentStep!` — semantic Cmd combinators in `src/Agdelte/Core/Cmd.agda`
- `examples_html/live-agent.html` — real-time dashboard: WS subscription + HTTP step buttons
- `examples_html/remote-agent.html` — Agda-compiled browser UI for RemoteAgent

Build commands:
- `npm run build:server` — compiles HttpAgent (single agent) to `_build/HttpAgent`
- `npm run build:multi-agent` — compiles MultiAgent (counter + toggle + WS) to `_build/MultiAgent`
- `npm run build:remote-agent` — compiles RemoteAgent browser app

**Key architecture decision:** Haskell via MAlonzo for server (real concurrency, STM, green threads), JS for browser (DOM, Web Workers). Same Agda source, two compilation targets.

**Not yet implemented (deferred to Phase 8+):**
- `ProcessOptic` — Optic over Unix sockets (IPC)
- `RemoteOptic` — Optic over HTTP
- Wiring diagrams — polynomial composition of agent networks
- Structured concurrency — parent cancellation cascading

See [architecture/dual-backend.md](../architecture/dual-backend.md), [architecture/concurrency.md](../architecture/concurrency.md).

**Files:**
| File | Role |
|------|------|
| `src/Agdelte/Concurrent/Agent.agda` | Pure Agent coalgebra (both backends) |
| `src/Agdelte/FFI/Server.agda` | Haskell FFI: IO, IORef, HTTP, AgentDef |
| `src/Agdelte/Core/Cmd.agda` | `agentQuery`/`agentStep!` combinators |
| `server/HttpAgent.agda` | Single-agent HTTP server |
| `server/MultiAgent.agda` | Multi-agent HTTP + WS server |
| `examples/RemoteAgent.agda` | Browser client for Agent server |
| `examples/Worker.agda` | Browser-side Web Worker |
| `hs/Agdelte/Http.hs` | Raw-socket HTTP server |
| `hs/Agdelte/WebSocket.hs` | Manual WS framing |
| `hs/Agdelte/AgentServer.hs` | Multi-agent server with STM broadcast |
| `examples_html/live-agent.html` | Real-time WS + HTTP dashboard |
| `examples_html/remote-agent.html` | RemoteAgent browser UI |

---

## Phase 8: Big Lens — Network-Wide Optic

Big Lens extends the Optic abstraction to span not just local widgets, but also server-side agents
and connected browser clients. The same `peek`/`over` interface works at every scale.

### Motivation

Phase 6 established optics for local widget composition:
```agda
-- Local: field access within one ReactiveApp
localOptic : Optic Model Item
localOptic = fromAffine (ixList n) ∘O fromLens itemsLens
```

Phase 7 established Agent as a server-side process with HTTP/WS interface.
But the interaction is ad-hoc: raw `httpGet`/`httpPost` with string paths.

Big Lens unifies everything: a single Optic can navigate from the server's
global state, through an agent's internal state, down to a widget on a connected browser client.

### Architecture

```
Big Lens
├── LocalOptic      (field access, Phase 6 ✅)
│     peek/over are direct function calls
│
├── AgentOptic      (server-side agent state)
│     peek = GET /agent/state
│     over = POST /agent/step
│     Transport: HTTP (or Unix socket for local processes)
│
├── ClientOptic     (connected browser client state)
│     peek = WS request → client responds with current model
│     over = WS push → client applies update to model
│     Transport: WebSocket
│
└── Composed        (chain of the above)
      peek/over traverse the entire network
```

### Key Idea: Browser Clients as Agents

A browser running a ReactiveApp is itself an Agent:
- **State** = Model
- **Observe** = view (current template rendering)
- **Step** = update (Msg → Model → Model)
- **Input** = Msg
- **Output** = the rendered DOM (or a serialized projection of Model)

The WebSocket connection already exists (Phase 7+ live-agent). What's missing is
the **protocol** for the server to peek at and push changes to connected clients.

```
Server                          Browser Client
  │                                   │
  │  WS: {"peek": "model.count"}     │
  │ ──────────────────────────────►   │
  │                                   │  reads model.count
  │  WS: {"value": "42"}             │
  │ ◄──────────────────────────────   │
  │                                   │
  │  WS: {"over": "Increment"}       │
  │ ──────────────────────────────►   │
  │                                   │  dispatches Increment msg
  │  WS: {"updated": "43"}           │
  │ ◄──────────────────────────────   │
```

This turns every connected browser into a node that the server can inspect and steer,
using the same Optic interface it uses for its own agents.

### Planned Deliverables

**8A: AgentOptic**
- `AgentOptic` type: Optic interface backed by HTTP GET/POST to Agent server
- `agentOptic : String → Optic AgentState AgentOutput` — construct from endpoint URL
- Composition: `agentOptic "/counter" ∘O fromLens valueLens` navigates into agent, then into its state
- Agda types for the protocol (request/response as data)
- Server-side: Agent already exposes state/step; add Optic-compatible wrapper

**8B: ClientOptic**
- Each WS-connected browser registers as a named client on the server
- Server can `peek` any client's model (request via WS, client responds)
- Server can `over` any client's model (push Msg via WS, client dispatches)
- `ClientOptic : String → Optic ClientModel A` — construct from client ID
- Browser runtime extension: handle incoming `peek`/`over` WS messages
- Client-side: `reactive.js` adds WS message handler that reads model or dispatches

**8C: Big Lens composition**
- Compose AgentOptic, ClientOptic, LocalOptic freely with `_∘O_`
- Example: server inspects `client["browser-1"].model.todoList[3].completed`
  ```agda
  bigLens : Optic ServerState Bool
  bigLens = clientOptic "browser-1"
          ∘O fromLens modelLens
          ∘O fromLens todoListLens
          ∘O fromAffine (ixList 3)
          ∘O fromLens completedLens
  ```
- This composes transport-agnostic: the runtime figures out which segments are local, which are WS, which are HTTP

**8D: Wiring diagrams**
- Polynomial composition of agents and clients as a wiring diagram
- Agent outputs connected to client inputs and vice versa
- Diagram defined in Agda, runtime interprets the connections
- Example: server agent state change → broadcast to all connected clients → each client re-renders
  (already works ad-hoc in Phase 7+; Big Lens makes it structured and composable)

### Relation to Theory

Big Lens is a **polynomial lens** `Lens P Q` where P and Q can be:
- **Monomial** (single agent/widget): `y^S` — one state, many directions
- **Sum** (multiple agents): `Σ_i y^(S_i)` — choose which agent
- **Product** (parallel composition): `y^(S₁ × S₂)` — both agents simultaneously

The composition `_∘O_` corresponds to polynomial lens composition.
Transport is encoded in the interpretation, not in the lens itself.

```
LocalOptic   = Lens (Mono S S) (Mono A A)           -- direct function
AgentOptic   = Lens (Mono S S) (Mono A A)           -- via HTTP
ClientOptic  = Lens (Mono S S) (Mono A A)           -- via WebSocket
Big Lens     = Lens (Mono S S) (Mono A A)           -- composed chain
             -- same type! Different interpretation.
```

This is the polynomial functor vision fully realized: the **same mathematical structure**
(polynomial lens) describes field access, process communication, and network-wide orchestration.

### What Already Exists (from Phase 7)

- WS broadcast: server pushes `"agentName:value"` to all clients on each step
- HTTP REST: `GET /agent/state`, `POST /agent/step` — already an implicit AgentOptic
- `wireAgent` in MultiAgent.agda: bridges pure Agent to mutable server runtime
- `agentQuery`/`agentStep!` in Cmd.agda: client-side of the interaction
- `live-agent.html`: browser subscribes to WS, displays state, sends HTTP steps

Phase 8 promotes these ad-hoc patterns to structured, composable optics.

### Implementation Notes for Continuation

To resume this work after context loss:

1. **Start with AgentOptic (8A)**: wrap existing HTTP `GET /state` + `POST /step` as an Optic.
   Create `src/Agdelte/Reactive/AgentOptic.agda` with `agentPeek` and `agentOver` that compile
   to `httpGet`/`httpPost` under the hood. The Optic record is already in `src/Agdelte/Reactive/Optic.agda`.

2. **Then ClientOptic (8B)**: extend the WS protocol in `hs/Agdelte/AgentServer.hs` to support
   `peek` and `over` messages to specific clients. Each client needs a unique ID (assigned on WS connect).
   On the browser side, extend `runtime/reactive.js` to handle incoming WS `peek` (respond with
   serialized model field) and `over` (dispatch a message into the update loop).

3. **Composition (8C)**: the key insight is that `_∘O_` already works for local optics.
   For network optics, the runtime needs to detect when a composed optic crosses a transport boundary
   and serialize/deserialize at that point. The Optic AST approach (similar to how Event/Cmd are ASTs
   interpreted by runtime) is the cleanest path.

4. **Wiring (8D)**: define a `Diagram` type in Agda that describes which agents connect to which
   clients and how. The server interprets the diagram to set up routing.

---

## Phase 9: Developer Experience

DevTools powered by Big Optic. Additional DOM effect primitives.

**Planned deliverables:**
- Network inspector — visualize widget/agent/client topology via Big Optic
- Time-travel debugging — record/replay state transitions (server + client)
- Hot reload — update code without losing state
- Cross-process inspection via AgentOptic/ClientOptic
- DOM effect Cmds: `setTitle`, `setDocumentTitle`, `focus` improvements

**Key idea:** Big Optic provides uniform access to every widget's, agent's, and client's state — local or remote — enabling powerful debugging tools with a single abstraction. The server can inspect any connected browser's model state in real-time.

---

## Phase 10: Formal Properties + Session Types

Mathematical rigor and formal correspondence.

**Planned deliverables:**
- Lens laws proofs (get-set, set-get, set-set)
- `Optic ≅ Poly.Lens` for monomial case — formal connection between practical optics and polynomial lenses
- `ReactiveApp ↔ Coalg` correspondence
- `Agent ↔ Coalg P` correspondence (Agent IS a coalgebra of `p(y) = O × (I → y)`)
- `Big Lens ↔ Poly.Lens` — network-wide optic as polynomial lens
- Dependent polynomial formalization
- Session type DSL — protocols that depend on interaction history
- Demo: multi-step form with typed state transitions
