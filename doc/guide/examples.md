# Agdelte Examples Guide

All examples use **Reactive Bindings** (like Svelte) — no Virtual DOM.

## Overview

| Example | Features | Complexity |
|---------|----------|------------|
| [Counter](#counter) | Reactive bindings, onClick | Simple |
| [Timer](#timer) | Event subs (interval) | Simple |
| [Todo](#todo) | foreach, when, input | Medium |
| [Keyboard](#keyboard) | Global keyboard events, styleBind | Medium |
| [Http](#http) | Cmd (httpGet), disabledBind | Medium |
| [Task](#task) | Task chains, do-notation | Medium |
| [WebSocket](#websocket) | wsConnect, wsSend, foreach | Medium |
| [Router](#router) | SPA routing, when | Medium |
| [Transitions](#transitions) | whenT, CSS enter/leave animations | Medium |
| [Composition](#composition) | zoomNode, shared total | Advanced |
| [Combinators](#combinators) | foldE, mapFilterE pipeline | Advanced |
| [Dynamic Optics](#dynamic-optics) | ixList, Traversal, runtime _∘O_, routeMsg | Advanced |
| [Session Form](#session-form) | Session protocol, phased state, typed transitions | Advanced |
| [Worker](#worker) | Web Worker, background computation | Medium |
| [Parallel](#parallel) | workerWithProgress, parallel, race | Advanced |
| [Stress Test](#stress-test) | 10K items, ops/sec, foreach, interval | Medium |
| [Remote Agent](#remote-agent) | Browser ↔ Haskell agent server | Advanced |
| [Agent Wiring](#agent-wiring) | >>>, &, ⊕, ***, fanout, loop, through, AgentLens | Theory |
| [Dep Agent](#dep-agent) | DepAgent, state-dependent input, embed, dep⊕, dep& | Theory |
| [Session Dual](#session-dual) | Session, dual, mkReqResp, mkOffer, dual-involution | Theory |
| [SharedAgent Demo](#sharedagent-demo) | share, asLinear, peekShared, stepShared, registry | Server |
| [Inspector Demo](#inspector-demo) | Diagram, inspectDiagram, wireSlot, refOptic, sendAndPrint | Server |

---

## Counter

**Demonstrates:** Reactive bindings (Svelte-style), direct DOM updates.

```agda
data Msg = Increment | Decrement | Reset

updateModel : Msg → ℕ → ℕ
updateModel Increment n = suc n
updateModel Decrement zero = zero
updateModel Decrement (suc n) = n
updateModel Reset _ = zero

counterTemplate : Node ℕ Msg
counterTemplate = div [ class "counter" ]
  ( h1 [] [ text "Agdelte Counter" ]
  ∷ div [ class "display" ] [ bindF show ]   -- auto-updates!
  ∷ div [ class "buttons" ]
      ( button (onClick Decrement ∷ class "btn" ∷ []) [ text "-" ]
      ∷ button (onClick Reset ∷ class "btn" ∷ []) [ text "Reset" ]
      ∷ button (onClick Increment ∷ class "btn" ∷ []) [ text "+" ]
      ∷ [] )
  ∷ [] )

app : ReactiveApp ℕ Msg
app = mkReactiveApp 0 updateModel counterTemplate
```

**Key point:** `bindF show` creates a reactive binding — DOM updates directly when model changes, no VDOM diffing.

---

## Timer

**Demonstrates:** Event subscriptions (interval), reactive text.

```agda
data Msg = Tick | Toggle | Reset

record Model : Set where
  field
    seconds : ℕ
    running : Bool

subs : Model → Event Msg
subs m = if running m then interval 1000 Tick else never

app : ReactiveApp Model Msg
app = mkReactiveApp initModel updateModel timerTemplate
```

**Key point:** `subs` returns different Event based on model state. Exported separately from `app`.

---

## Todo

**Demonstrates:** `foreachKeyed` for keyed list reconciliation, `when` for conditional rendering, input handling.

```agda
record Todo : Set where
  field
    todoId    : ℕ
    todoText  : String
    completed : Bool

todoTemplate : Node Model Msg
todoTemplate = div [ class "todo-app" ]
  ( ...
  ∷ ul [ class "todo-list" ]
      [ foreachKeyed todos todoKey viewTodoItem ]  -- keyed reconciliation!
  ∷ when hasTodos (
      div [ class "footer" ] [ ... ]   -- conditional footer
    )
  ∷ [] )
```

**Key point:** `foreachKeyed` uses keys for efficient reconciliation — same key reuses DOM node, removed key destroys node. No full list rebuild.

---

## Keyboard

**Demonstrates:** Global keyboard event handling, `styleBind` for dynamic styles.

```agda
subs : Model → Event Msg
subs _ = onKeyDown handleKey
  where
    handleKey : KeyboardEvent → Maybe Msg
    handleKey ke with key ke
    ... | "ArrowUp"    = just MoveUp
    ... | "ArrowDown"  = just MoveDown
    ... | "ArrowLeft"  = just MoveLeft
    ... | "ArrowRight" = just MoveRight
    ... | _            = nothing

-- Dynamic position via styleBind
styles (name "left") (λ m → showNat (posX m) ++ "px")
styles (name "top")  (λ m → showNat (posY m) ++ "px")
```

**Key point:** `onKeyDown` with Maybe — filter keys at subscription level. `styleBind` for reactive CSS.

---

## Http

**Demonstrates:** HTTP requests via Cmd, `disabledBind` for reactive button state.

```agda
data Msg = Fetch | GotData String | GotError String

cmd : Msg → Model → Cmd Msg
cmd Fetch _ = httpGet "/api/data" GotData GotError
cmd _ _ = ε

updateModel : Msg → Model → Model
updateModel Fetch m = record m { status = "Loading..." }
updateModel (GotData d) m = record m { status = d }
updateModel (GotError e) m = record m { status = "Error: " ++ e }
```

**Key point:** `updateModel` stays simple, HTTP logic in `cmd`. Exported separately.

---

## Task

**Demonstrates:** Sequential HTTP chains with do-notation.

```agda
fetchChain : Task String
fetchChain = do
  user ← http "/api/user"
  posts ← http ("/api/users/" ++ user ++ "/posts")
  pure (combine user posts)

cmd : Msg → Model → Cmd Msg
cmd Fetch _ = attempt fetchChain GotResult
cmd _ _ = ε
```

**Key point:** `Task` monad for sequential operations, `attempt` to run.

---

## WebSocket

**Demonstrates:** WebSocket connection, `foreach` for message list, `when` for conditional UI.

```agda
subs : Model → Event Msg
subs m = if wantConnected m then wsConnect wsUrl WsEvent else never

cmd : Msg → Model → Cmd Msg
cmd Send m = if connected m then wsSend wsUrl (input m) else ε
cmd _ _ = ε

-- Message list with foreach
foreach messages viewMessage
-- Conditional connected status
when isConnected (div [ class "status" ] [ text "Connected" ])
```

**Key point:** Separate `wantConnected` (intent) from `connected` (status) to prevent subscription cycling.

---

## Router

**Demonstrates:** SPA routing with `when` for conditional page rendering.

```agda
data Route = Home | About | NotFound

subs : Model → Event Msg
subs _ = onUrlChange (UrlChanged ∘ parseRoute)

cmd : Msg → Model → Cmd Msg
cmd (Navigate r) _ = pushUrl (routeToUrl r)
cmd _ _ = ε

-- Conditional pages with when
when isHome (div [] [ text "Welcome!" ])
when isAbout (div [] [ text "About page" ])
```

**Key point:** `when` replaces conditional rendering. `pushUrl` for navigation, `onUrlChange` for popstate events.

---

## Transitions

**Demonstrates:** `whenT` with CSS enter/leave transitions. Auto-dismiss via `timeout`.

```agda
panelTrans : Transition
panelTrans = mkTransition "panel-enter" "panel-leave" 300

notifTrans : Transition
notifTrans = mkTransition "notif-enter" "notif-leave" 400

-- Toggle panel with slide transition
whenT panelOpen panelTrans
    (div [ class "panel" ] [ ... ])

-- Notification toast with auto-dismiss
whenT notifVisible notifTrans
    (div [ class "notification" ] [ ... ])

subs : Model → Event Msg
subs m = if notifVisible m then timeout 3000 AutoDismiss else never
```

**Key point:** `whenT` adds CSS enter/leave classes. Runtime waits `duration` ms before removing DOM node on leave. `Transition` record: `enterClass`, `leaveClass`, `duration`.

---

## Composition

**Demonstrates:** Two counters composed with shared total via `zoomNode`.

```agda
-- Shared model
record Model : Set where
  field
    counter1 : ℕ
    counter2 : ℕ

data Msg = LeftMsg CounterMsg | RightMsg CounterMsg

-- Reuse counter template with zoomNode (maps model AND messages)
zoomNode counter1 LeftMsg counterTemplate
zoomNode counter2 RightMsg counterTemplate

-- Shared total binding
bindF (λ m → show (counter1 m + counter2 m))
```

**Key point:** `zoomNode` maps both model AND messages — child templates are fully reusable without manual wrapping.

---

## Combinators

**Demonstrates:** `foldE` + `mapFilterE` stateful event pipeline.

```agda
-- Pipeline: interval 300ms → foldE (count internally) → mapFilterE (classify)
subs : Model → Event Msg
subs m = if running m
  then mapFilterE classify (foldE 0 (λ _ n → suc n) (interval 300 tt))
  else never
  where
    classify : ℕ → Maybe Msg
    classify n = if isBatch n then just (BatchTick n) else just Tick

isBatch : ℕ → Bool
isBatch n = (n % 5) ≡ᵇ 0
```

**Key point:** `foldE` maintains internal state (tick counter) invisible to the model. `mapFilterE` classifies each tick into `Tick` or `BatchTick`. The pipeline demonstrates stateful event transformation.

---

## Dynamic Optics

**Demonstrates:** Runtime optic composition with `ixList`, `Traversal`, `_∘O_`, `peek`.

```agda
-- Dynamic optic: target depends on runtime state (selected index)
nthItemOptic : ℕ → Optic Model Item
nthItemOptic n = fromAffine (ixList n) ∘O fromLens itemsLens

-- Inc selected item: optic composed at runtime
updateModel IncSelected m = over (nthItemOptic (selected m)) incValue m

-- Reset ALL items: traversal for batch operation
updateModel ResetAll m = over (fromTraversal allItemsTraversal) resetValue m

-- Safe peek: Affine may fail (index out of bounds)
selectedText m with peek (nthItemOptic (selected m)) m
... | nothing   = "Selected: (none)"
... | just item = "Selected: " ++ itemLabel item
```

**Key point:** Unlike static `Lens` (always succeeds), `ixList` returns `Affine` (may fail). Optics compose at runtime via `_∘O_` — the navigation target changes based on user interaction. `Traversal.overAll` enables batch operations over the entire collection.

---

## Session Form

**Demonstrates:** Multi-step form with typed state transitions using Session protocol concepts from `SessionExec`.

```agda
-- Session protocol (conceptual):
--   recv Name → recv Email → recv Age → send Summary → done

data FormPhase : Set where
  enterName  : FormPhase
  enterEmail : FormPhase
  enterAge   : FormPhase
  confirm    : FormPhase
  submitted  : FormPhase

record Model : Set where
  field
    phase    : FormPhase
    name     : String
    email    : String
    age      : String
    curInput : String
    stepNum  : ℕ

-- Submit: typed transition per phase
submitStep : Model → Model
submitStep m with phase m
... | enterName  = mkModel enterEmail (curInput m) (email m) (age m) "" 2
... | enterEmail = mkModel enterAge (name m) (curInput m) (age m) "" 3
... | enterAge   = mkModel confirm (name m) (email m) (curInput m) "" 4
... | confirm    = mkModel submitted (name m) (email m) (age m) "" 5
... | submitted  = m

-- Conditional rendering per phase
when isInputPhase (div [] [ input [...], button [...] ])
when isConfirm    (div [] [ summary, button "Submit" ])
when isSubmitted  (div [] [ success message ])
```

**Key point:** The `FormPhase` type encodes session protocol progress. Each phase has typed transitions — `enterName` only saves to `name`, `enterEmail` only saves to `email`. The `when` combinator renders different UI per phase. This is the Agent/SessionExec pattern (phased state machine) applied to a ReactiveApp.

---

## Worker

**Demonstrates:** Offloading heavy computation to a Web Worker background thread.

```agda
-- Worker computes fibonacci, main thread stays responsive
subs : Model → Event Msg
subs m = if computing m
  then worker "/workers/fib.js" (show n) GotResult GotError
  else never
```

**Key point:** `worker` spawns a separate thread. Main thread UI stays responsive during heavy computation.

---

## Parallel

**Demonstrates:** `workerWithProgress`, `parallel`, `race`, `raceTimeout` combinators.

```agda
-- Worker with progress updates
workerWithProgress "/workers/heavy.js" input GotResult GotError GotProgress

-- Parallel HTTP requests, collect all
parallel [ httpGet url1 id id, httpGet url2 id id ] combine

-- Race: first to finish wins
race [ httpGet fast id id, httpGet slow id id ]
```

**Key point:** Concurrency combinators compose declaratively. `parallel` collects all results, `race` takes the first.

---

## Stress Test

**Demonstrates:** Pure dispatch throughput. Measures ops/sec with 13 simultaneous reactive bindings.

```agda
-- Each tick: increment counter, compute 4 modular bindings
updateModel Tick m =
  let c = suc (counter m)
  in record m
    { counter = c ; ticks = suc (ticks m) ; totalOps = suc (totalOps m)
    ; b1 = c % 7 ; b2 = c % 13 ; b3 = c % 37 ; b4 = c % 97 }

-- interval 1ms for max throughput, 1000ms to measure ops/sec
subs m = if running m
  then merge (interval 1 Tick) (interval 1000 Measure)
  else never

-- 13 bindF bindings update simultaneously, bar visualization
div [ class "binding-row" ]
  ( span [] [ bindF b1text ]
  ∷ span [] [ bindF b1bar ]    -- █ blocks visualize mod value
  ∷ [] )
```

**Key point:** Each dispatch cycle updates 13 bindings in O(13), not O(n). No Virtual DOM, no diffing, no tree rebuild. Shows ops/sec and peak throughput with live bar visualization.

---

## Remote Agent

**Demonstrates:** Browser client talking to a Haskell agent server via fetch API.

```agda
-- Query remote agent state
cmd Query _ = agentQuery "/api/agent/state" GotState GotError

-- Step remote agent
cmd (Step input) _ = agentStep "/api/agent/step" input GotState GotError
```

**Key point:** `agentQuery`/`agentStep` use the Big Lens protocol (peek/over) to interact with server-side agents.

---

## Agent Wiring

**Demonstrates:** All `Wiring.agda` combinators with step-by-step verification proofs. Pure Agda (no HTML).

```agda
-- Pipeline: counter >>> classifier
pipeline : Agent (ℕ × ℕ) ⊤ String
pipeline = counter >>> classifier

-- External choice: counter & classifier
both : Agent (ℕ × ℕ) (⊤ ⊎ ℕ) (ℕ × String)
both = counter & classifier

-- AgentLens: interface transformation
myLens : AgentLens ⊤ ℕ ⊤ String
myLens = mkAgentLens show (λ _ _ → tt)

adapted : Agent ℕ ⊤ String
adapted = through myLens counter
```

**Key point:** Covers `>>>`, `&`, `⊕`, `***`, `fanout`, `loop`, `through`, `selectLeft`/`selectRight`, `mkAgentLens`, `mapI`/`mapO`/`remap`, `SomeAgent`/`pack`/`>>>ₛ`. All operations verified with `≡ refl` proofs.

Source: `examples/AgentWiring.agda`

---

## Dep Agent

**Demonstrates:** `DepAgent` — dependent polynomial coalgebra where input type depends on observation. Pure Agda (no HTML).

```agda
-- Vending machine: commands depend on phase
data Phase : Set where
  idle  : Phase    -- accepts Insert (⊤)
  ready : Phase    -- accepts Select (String)

Cmd : Phase → Set
Cmd idle  = ⊤
Cmd ready = String

vendingMachine : DepAgent VendState Phase Cmd
```

**Key point:** In `idle` phase, only `⊤` (insert coin) is accepted. In `ready` phase, only `String` (select product) is accepted. Wrong-phase commands are rejected by the type checker. Also shows `embed` (Agent → DepAgent), `dep⊕` (exact internal choice), `dep&` (exact external choice), `throughDep` + `DepAgentLens` (interface transformation).

Source: `examples/DepAgentDemo.agda`

---

## Session Dual

**Demonstrates:** Dual session types with formal duality proofs. Pure Agda (no HTML).

```agda
-- Key-value store protocol
KVProto : Session
KVProto = offer GetProto PutProto

-- Client sees the dual automatically
ClientKVProto : Session
ClientKVProto = dual KVProto

-- Type-level guarantee: what server sends, client receives
_ : SessionO GetProto ≡ SessionI (dual GetProto)
_ = refl

-- Duality is an involution (imported from Theory)
_ : dual (dual KVProto) ≡ KVProto
_ = dual-involution KVProto
```

**Key point:** `dual` automatically flips send↔recv, offer↔choose. The type system guarantees server output matches client input. `dual-involution` proves `dual (dual s) ≡ s` for any session. Also shows `mkReqResp`, `mkOffer`, `selectLeft`/`selectRight`, `SessionAgent`.

Source: `examples/SessionDual.agda`

---

## SharedAgent Demo

**Demonstrates:** Multiplicity markers (`share`, `asLinear`), `peekShared`/`stepShared`, `useLinear`, shared agent composition (`>>>shared`, `***shared`, `fanoutShared`), `Registry`/`lookupAgent`. Haskell-compiled (no browser).

```agda
-- Wrap agents with multiplicity witness
sharedCounter : SharedAgent String String
sharedCounter = share counterAgent

linearEcho : LinearAgent String String
linearEcho = asLinear echoAgent

-- Compose: pipeline, parallel, fanout
pipelined = sharedEcho >>>shared sharedBang    -- echo → add "!"
parallel  = sharedCounter ***shared sharedAcc  -- independent pair
fanned    = fanoutShared sharedCounter sharedAcc  -- same input to both

-- Registry: named collection of shared agents
registry : Registry
registry = mkNamed "counter" "/counter" sharedCounter
         ∷ mkNamed "accumulator" "/acc" sharedAcc ∷ []

lookupAgent "counter" registry  -- → just (...)
```

**Key point:** `SharedAgent` is the type-level witness that an agent can serve multiple clients. `LinearAgent` is consumed after one use. Composition combinators (`>>>shared`, `***shared`, `fanoutShared`) preserve multiplicity. `Registry` enables named lookup.

```bash
npm run build:shared-demo && npm run run:shared-demo
```

Source: `server/SharedAgentDemo.agda`

---

## Inspector Demo

**Demonstrates:** `Diagram` construction (`singleAgent`, `dualAgent`, `pipeline`, `_⊕D_`), `inspectDiagram` to peek all agent states, `wireSlot` to bridge pure Agent to mutable IO, `refOptic` for IORef-backed IOOptic, `sendAndPrint` for command dispatch. Haskell-compiled (no browser).

```agda
-- Build diagrams declaratively
counterDiagram  = singleAgent "counter" "/counter" counterAgent 3001
dualDiagram     = dualAgent "counter" "/counter" counterAgent
                            "echo"    "/echo"    echoAgent 3002
pipelineDiagram = pipeline "echo" "/echo" echoAgent
                           "bang" "/bang" bangAgent 3003
mergedDiagram   = (counterDiagram ⊕D pipelineDiagram) 3004

-- Inspect all agents in a diagram
inspectDiagram counterDiagram
-- Output:
--   === Network Inspector ===
--   Agents: 1
--     counter: 0
--   =========================

-- Bridge to mutable IO and inspect via IOOptic
wireSlot (mkSlot "counter" "/counter" counterAgent) >>= λ def → ...
newIORef "initial-value" >>= λ ref →
ioPeek (refOptic ref)    -- → just "initial-value"
ioOver (refOptic ref) "new"  -- updates IORef, returns "new"
```

**Key point:** `Diagram` is the declarative topology — slots + connections. `inspectDiagram` uses `IOOptic` (Big Lens) to peek each agent. `wireSlot` bridges pure `Agent` coalgebra to mutable `AgentDef` for the server runtime. `_⊕D_` merges two diagrams.

```bash
npm run build:inspector-demo && npm run run:inspector-demo
```

Source: `server/InspectorDemo.agda`

---

## Running Examples

```bash
# Build all
npm run build:all

# Start server
npm run dev

# Open in browser
http://localhost:8080/                              # Index
http://localhost:8080/examples_html/counter.html
http://localhost:8080/examples_html/timer.html
http://localhost:8080/examples_html/todo.html
http://localhost:8080/examples_html/keyboard.html
http://localhost:8080/examples_html/http.html
http://localhost:8080/examples_html/task.html
http://localhost:8080/examples_html/websocket.html
http://localhost:8080/examples_html/router.html
http://localhost:8080/examples_html/transitions.html
http://localhost:8080/examples_html/composition.html
http://localhost:8080/examples_html/combinators.html
http://localhost:8080/examples_html/optic-dynamic.html
http://localhost:8080/examples_html/worker.html
http://localhost:8080/examples_html/parallel.html
http://localhost:8080/examples_html/remote-agent.html
http://localhost:8080/examples_html/session-form.html
http://localhost:8080/examples_html/stress-test.html

# Server examples (Haskell-compiled, run in terminal)
npm run build:shared-demo && npm run run:shared-demo
npm run build:inspector-demo && npm run run:inspector-demo
```

## Structure Pattern

Every example follows this pattern:

```agda
module MyExample where

-- 1. Imports
open import Agdelte.Reactive.Node

-- 2. Model
Model = ℕ  -- or record

-- 3. Messages
data Msg : Set where ...

-- 4. Update (pure!)
updateModel : Msg → Model → Model

-- 5. Template (declarative structure with bindings!)
template : Node Model Msg
template = div [ class "example" ]
  ( ... [ bindF showValue ]  -- reactive binding
  ∷ button [ onClick SomeMsg ] [ text "Click" ]
  ∷ [] )

-- 6. App
app : ReactiveApp Model Msg
app = mkReactiveApp init updateModel template

-- 7. Optional: subs, cmd (exported separately)
subs : Model → Event Msg
cmd : Msg → Model → Cmd Msg
```

**Key difference from Virtual DOM**: `template` is data (not a function), bindings track which DOM nodes to update.
