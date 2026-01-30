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
| 7 | Concurrency + Distribution | ✅ Done | Agent, Wiring, Session, dual-backend, HTTP+WS, Multi-Agent |
| 8 | Big Lens (network-wide) | Planned | Big Lens across local widgets, server agents, and browser clients |
| 9 | Developer Experience | Planned | DevTools via Big Optic, time-travel, hot reload |
| 10 | Formal Properties | Planned | Optic ≅ Poly.Lens, lens laws, dual involution proof |

See [api.md](api.md) for full API reference of all implemented features (Phases 1–7).

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

The WebSocket connection already exists (Phase 7 live-agent). What's missing is
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
  (already works ad-hoc in Phase 7; Big Lens makes it structured and composable)

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

## Phase 10: Formal Properties

Mathematical rigor and formal correspondence.

**Planned deliverables:**
- Lens laws proofs (get-set, set-get, set-set)
- `Optic ≅ Poly.Lens` for monomial case — formal connection between practical optics and polynomial lenses
- `ReactiveApp ↔ Coalg` correspondence
- `Agent ↔ Coalg P` correspondence (Agent IS a coalgebra of `p(y) = O × (I → y)`)
- `Big Lens ↔ Poly.Lens` — network-wide optic as polynomial lens
- Dependent polynomial formalization
- `dual (dual s) ≡ s` — session type involution proof
- Recursive/coinductive sessions — looping protocols (see [research.md](research.md))
- Multi-step session execution — Agent pipeline via `_>>>_`
- Demo: multi-step form with typed state transitions
