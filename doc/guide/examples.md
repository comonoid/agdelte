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
| [CSS Demo](#css-demo) | Stylesheet, rule, media, keyframeRule, renderStylesheet | CSS |
| [CSS Full Demo](#css-full-demo) | All CSS features: variables, layout, transitions, animations | CSS |
| [Anim Demo](#anim-demo) | Tween, Spring, compile-time verification | CSS |
| [SVG Test](#svg-test) | SVG namespace, typed attributes, reactive bindings | SVG |
| [SMIL Animations](#smil-animations) | Declarative animations, choreography, motion paths | SVG |
| [SVG Pan/Zoom](#svg-panzoom) | Interactive viewport, SVG events, coordinate conversion | SVG |
| [SVG Bar Chart](#svg-bar-chart) | Data visualization, foreach, reactive bindings | SVG |
| [Line Drawing](#line-drawing) | Stroke-dasharray trick, SMIL animate | SVG |
| [WebGL Test](#webgl-test) | Perspective camera, phong, animate, bindTransform, onClick | WebGL |
| [WebGL Full Demo](#webgl-full-demo) | All WebGL features: cameras, materials, lights, text3D, groups, events | WebGL |
| [WebGL Controls Demo](#webgl-controls-demo) | 3D UI controls: buttons, toggles, text3D from Controls library | WebGL |

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

## Building Server Examples

Server examples require GHC (Haskell compiler) and compile via Agda's GHC backend.

### Prerequisites

```bash
# Install GHC and cabal
# Ubuntu/Debian:
sudo apt install ghc cabal-install

# macOS:
brew install ghc cabal-install

# Update cabal package list
cabal update
```

### Build & Run

```bash
# HttpAgent (simple HTTP server)
npm run build:server && _build/Main

# SharedAgent Demo
npm run build:shared-demo && _build/SharedAgentDemo

# Inspector Demo
npm run build:inspector-demo && _build/InspectorDemo

# MultiAgent (requires multiple terminals)
npm run build:multi-agent && _build/MultiAgent
```

### Haskell Support Modules

Server examples use Haskell FFI modules in `hs/`:
- `Http.hs` — HTTP server primitives
- `WebSocket.hs` — WebSocket support
- `AgentServer.hs` — Agent server wiring

---

## CSS Demo

**Demonstrates:** Static CSS generation from Agda. `Stylesheet`, `rule`, `media`, `keyframeRule`, `renderStylesheet`.

```agda
open import Agdelte.Css
open import Agdelte.Css.Stylesheet
open import Agdelte.Css.Animate (fadeIn)

appCSS : Stylesheet
appCSS =
    rawRule "@charset \"UTF-8\";"
  ∷ rule ".card" (
        padding' (px 16) ∷ backgroundColor' (hex "#fff")
      ∷ borderRadius' (px 8)
      ∷ transition' (trans "box-shadow" (ms 200) ease
                   ∷ trans "transform" (ms 200) ease ∷ [])
      ∷ "cursor" ∶ "pointer" ∷ [])
  ∷ rule ".card:hover" (
        "box-shadow" ∶ "0 8px 24px rgba(0,0,0,0.3)"
      ∷ "transform" ∶ "translateY(-2px)" ∷ [])
  ∷ media "(max-width: 768px)" (
      rule ".card" (padding' (px 8) ∷ []) ∷ [])
  ∷ keyframeRule fadeIn
  ∷ []
```

**Build pipeline:**

```bash
npm run build:css-demo     # Agda -> JS
npm run css:demo           # JS -> css-demo.css
```

**Key point:** `renderStylesheet` is a pure function. The Agda compiler evaluates the `Stylesheet` value, the JS backend emits it as data, and `generate-css.js` calls `renderStylesheet` to produce a plain `.css` file. No runtime CSS injection.

Source: `examples/CssDemo.agda`

---

## CSS Full Demo

**Demonstrates:** All CSS features end-to-end: typed properties, composition, variables, layout helpers, conditional styles, transitions, animations, media queries, and stylesheet generation.

```agda
-- CSS variables
themeVars : Style
themeVars = cssVar "primary" "#4a9eff" ∷ cssVar "radius" "8px" ∷ []

-- Typed properties with variable references
themedCard : Style
themedCard = color' (named "white") ∷ backgroundColor' (var "primary")
           ∷ "border-radius" ∶ varRef "radius" ∷ []

-- Conditional styles
cardStyle : Bool → Style
cardStyle active = styleWhen active
  ("border" ∶ "2px solid var(--primary)" ∷ [])
  ("border" ∶ "2px solid transparent" ∷ [])

-- Layout
toolbar : Style
toolbar = row <> center <> "padding" ∶ "0.5rem" ∷ []

-- Transitions + animations
hoverTransition : Decl
hoverTransition = transition' (trans "all" (ms 200) ease ∷ [])

-- Full stylesheet
appCSS : Stylesheet
appCSS = rule ":root" themeVars
       ∷ rule ".card" (padding' (px 16) ∷ hoverTransition ∷ [])
       ∷ media "(max-width: 768px)" (rule ".card" (padding' (px 8) ∷ []) ∷ [])
       ∷ keyframeRule fadeIn ∷ keyframeRule pulse ∷ keyframeRule spin
       ∷ []
```

**Build pipeline:**

```bash
npm run build:css-full-demo   # Agda -> JS
npm run css:full-demo         # JS -> css-full-demo.css
```

**Key point:** Covers the entire CSS DSL surface. The generated `.css` file is used by the HTML page via `<link>`. No JavaScript imports of Agda modules at runtime.

Source: `examples/CssFullDemo.agda`

---

## Anim Demo

**Demonstrates:** Compile-time verification of `Tween` and `Spring` physics. Pure Agda computation, no browser runtime.

```agda
open import Agdelte.Anim.Tween
open import Agdelte.Anim.Spring

-- Tween: opacity 0->1 over 300ms with easeOut
opacityTween : Tween Float
opacityTween = record
  { elapsed = 0 ; duration = 300 ; from = 0.0 ; to = 1.0
  ; easing = easeOutFn ; lerp = floatLerp }

opacityMid : Tween Float × Float
opacityMid = tickTween opacityTween 150      -- advance 150ms
opacityMidValue = proj₂ opacityMid           -- ≈ 0.875

-- Spring: gentle 0->1
dialogSpring : Spring
dialogSpring = gentle 0.0 1.0

dialogFrame1 = tickSpringStable dialogSpring 16  -- position ≈ 0.031
dialogSettled = isSettled (iterate 80 ...)         -- true after ~1.3s

-- Retarget mid-flight
retargetedSpring = retarget 2.0 (tickSpringStable (bouncy 0.0 1.0) 50)
```

**Build pipeline:**

```bash
npm run build:anim-demo   # Agda -> JS (values computed at compile time)
npm run css:anim-data     # Extract computed values to JSON
```

The HTML page loads `anim-demo.json` and displays a verification table (each value checked against expected ranges) plus a bar chart visualization. This is not a runtime animation demo -- it verifies that the Tween/Spring math is correct by inspecting compile-time computed values.

**Key point:** Since Tween and Spring are pure functions, the Agda compiler evaluates them during compilation. The JSON file contains baked-in numbers, not code. In a real app these values would drive `styleBind` each frame.

Source: `examples/AnimDemo.agda`

---

## SVG Test

**Demonstrates:** Basic SVG rendering with namespace-aware elements, typed attributes, and reactive bindings.

```agda
open import Agdelte.Svg

svgTemplate : Node Model Msg
svgTemplate =
  svg (viewBox_ "0 0 200 200" ∷ width_ "200" ∷ height_ "200" ∷ [])
    ( rect' (x_ "0" ∷ y_ "0" ∷ width_ "200" ∷ height_ "200" ∷ fillC (hex "#f0f0f0") ∷ []) []
    ∷ circle' (cxF 100.0 ∷ cyF 100.0
              ∷ attrBind "r" (stringBinding λ m → show (radius m))
              ∷ fillC (hex "#4a9eff") ∷ []) []
    ∷ [])
```

**Key point:** `Agdelte.Svg` re-exports all SVG modules. Elements use `createElementNS` with SVG namespace automatically. Typed attributes (`cxF`, `fillC`) provide compile-time validation.

Source: `examples/SvgTest.agda`

---

## SMIL Animations

**Demonstrates:** Declarative SVG animations without JavaScript: choreographed sequences, click triggers, hover effects, motion paths.

```agda
open import Agdelte.Svg

-- Choreographed sequence: fade in → pulse → color shift
circle' (cxF 150.0 ∷ cyF 100.0 ∷ rF 30.0 ∷ opacity_ "0" ∷ [])
  ( animate "opacity" "0" "1"
      (freezeEnd (withId "fadeIn" (record defaultSmil { dur = ms 800 })))
  ∷ animateValues "r" ("30" ∷ "40" ∷ "30" ∷ [])
      (withId "pulse" (record defaultSmil { dur = ms 600 ; begin' = syncEnd "fadeIn" }))
  ∷ animate "fill" "#4a9eff" "#ff6b6b"
      (freezeEnd (record defaultSmil { dur = ms 400 ; begin' = syncEnd "pulse" }))
  ∷ [])

-- Click to expand
circle' (cxF 150.0 ∷ cyF 250.0 ∷ rF 25.0 ∷ [])
  ( animate "r" "25" "50"
      (freezeEnd (onClick' (record defaultSmil { dur = ms 300 })))
  ∷ [])
```

**Key point:** SMIL animations are declarative — the browser handles timing and interpolation. `syncEnd`, `syncBegin`, `onClick'` create choreographed sequences. No JavaScript animation loop needed. The runtime automatically starts animations with numeric or syncbase timing when DOM is created.

Source: `examples/SvgSmil.agda`

---

## SVG Pan/Zoom

**Demonstrates:** Interactive SVG viewport manipulation with pointer events and coordinate conversion.

```agda
open import Agdelte.Svg

record Model : Set where
  field viewBox : ViewBox ; isDragging : Bool ; lastX lastY : Float

updateModel (Drag p) m with isDragging m
... | true =
  let dx = Point.x p - lastX m
      dy = Point.y p - lastY m
  in record m { viewBox = panViewBox (0.0 - dx) (0.0 - dy) (viewBox m) ; ... }

panZoomTemplate =
  svg ( attrBind "viewBox" (stringBinding λ m → showViewBox (viewBox m))
      ∷ onSvgPointerDown StartDrag
      ∷ onSvgPointerMove Drag
      ∷ onSvgPointerUp (λ _ → StopDrag)
      ∷ [])
    (... shapes ...)
```

**Key point:** `onSvgPointerDown/Move` handlers receive coordinates in SVG space (via `getScreenCTM().inverse()`). `panViewBox`/`zoomViewBox` manipulate the ViewBox directly.

Source: `examples/SvgPanZoom.agda`

---

## SVG Bar Chart

**Demonstrates:** Data visualization with `foreach`, reactive bindings, and interactive selection.

```agda
open import Agdelte.Svg

record BarData : Set where
  field barLabel : String ; barValue : ℕ ; barColor : Color

renderBar : BarData × ℕ → ℕ → Node Model Msg
renderBar (bar , idx) _ =
  g (onClick (SelectBar idx) ∷ [])
    ( rect' ( xF xPos
            ∷ attrBind "y" (stringBinding λ m → ...)
            ∷ attrBind "height" (stringBinding λ m → ...)
            ∷ attrBind "fill" (stringBinding λ m →
                if idx ≡ᵇ selectedIdx m then "#1e40af" else getColorAt idx (bars m))
            ∷ []) []
    ∷ svgText (...) [ bind (stringBinding λ m → show (getValueAt idx (bars m))) ]
    ∷ [] )

chartTemplate =
  svg (...)
    ( yAxis ∷ foreach (λ m → indexBars (bars m)) renderBar ∷ [] )
```

**Key point:** `foreach` generates bars from model data. Each bar has reactive bindings for position, height, and color. Click events update selection.

Source: `examples/SvgChart.agda`

---

## Line Drawing

**Demonstrates:** Self-drawing paths using stroke-dasharray/dashoffset trick with SMIL animation.

```agda
open import Agdelte.Svg

starPath = "M150 20 L179 90 L255 90 L194 140 L218 215 L150 170 L82 215 L106 140 L45 90 L121 90 Z"
starLength = 530.0

drawingPathSmil pathD len strokeColor =
  path' ( d_ pathD
        ∷ stroke_ strokeColor ∷ fill_ "none"
        ∷ attr "stroke-dasharray" (showFloat len)
        ∷ attr "stroke-dashoffset" (showFloat len)  -- start hidden
        ∷ [])
    ( animate "stroke-dashoffset" (showFloat len) "0"
        (freezeEnd (record defaultSmil { dur = sec 2.0 ; begin' = onEvent "click" }))
    ∷ [] )
```

**Key point:** `stroke-dasharray = pathLength` with `stroke-dashoffset` transitioning from pathLength to 0 creates the drawing effect. SMIL animates the dashoffset smoothly.

Source: `examples/SvgLineDraw.agda`

---

## WebGL Test

**Demonstrates:** Basic 3D scene with perspective camera, phong/unlit materials, lights, interactive objects, transitions, continuous animation.

```agda
open import Agdelte.WebGL.Types
  renaming (onClick to glClick)

scene : Scene Model Msg
scene = mkScene
  (fixed (perspective 1.0 0.1 100.0) (vec3 0.0 2.0 8.0) (vec3 0.0 0.0 0.0))
  ( light (ambient white 0.15)
  ∷ light (directional white 0.9 (vec3 -0.5 -1.0 -0.3))
  ∷ mesh (sphere 0.9) (phong (rgb 0.2 0.5 0.8) 64.0) [ glClick ClickLeft ]
      (mkTransform (vec3 -2.5 0.0 0.0) identityQuat (vec3 1.0 1.0 1.0))
  ∷ bindTransform centerTransform
      (bindMaterial centerMaterial (box (vec3 1.5 1.5 1.5))
         (glClick ClickCenter ∷ transition (ms 300) easeInOut ∷ [])
         identityTransform)
  ∷ animate orbitTransform
      (mesh (sphere 0.4) (phong (rgb 0.9 0.8 0.2) 128.0) [] identityTransform)
  ∷ [] )

webglTemplate : Node Model Msg
webglTemplate =
  div [ class "webgl-demo" ]
    ( h1 [] [ text "Agdelte WebGL" ]
    ∷ glCanvas (attr "width" "800" ∷ attr "height" "600" ∷ []) scene
    ∷ ... )
```

**Key point:** `Scene` is a declarative scene graph: `mkScene Camera (List SceneNode)`. `bindTransform`/`bindMaterial` create reactive 3D bindings (same concept as DOM `bind`, but for transforms and materials). `animate` receives elapsed time as Float for continuous motion. `glCanvas` embeds the scene in the DOM template.

Source: `examples/WebGLTest.agda`

---

## WebGL Full Demo

**Demonstrates:** All remaining WebGL features: `fromModel` reactive camera (ortho/perspective switching), `pbr`/`flat`/`textured` materials, `point`/`spot` lights, `bindLight`, `icon`, `text3D`/`bindText3D`, `group`, `onHover`/`onLeave`, `onScroll`, `onClickAt`, `onDrag`, `focusable`/`onKeyDown`.

```agda
open import Agdelte.WebGL.Types
  renaming (onClick to glClick; onHover to glHover; onLeave to glLeave;
            onScroll to glScroll; onClickAt to glClickAt; onDrag to glDrag;
            focusable to glFocusable; onKeyDown to glKeyDown)

scene : Scene Model Msg
scene = mkScene
  -- Reactive camera: switches ortho/perspective from model
  (fromModel cameraProjection cameraPos cameraTarget)
  ( light (ambient (rgb 0.3 0.3 0.4) 0.3)
  ∷ light (spot (rgb 0.8 0.8 1.0) 0.7 (vec3 -3.0 5.0 0.0) ...)
  ∷ bindLight pointLightFromModel    -- reactive light intensity!
  -- PBR sphere with hover
  ∷ bindMaterial pbrMaterial (sphere 0.8)
      (glClick (SelectObj 1) ∷ glHover (HoverObj 1) ∷ glLeave (LeaveObj 1) ∷ ...)
      ...
  -- Textured box with surface click
  ∷ mesh (box ...) (textured (loadTexture "textures/crate.png") white)
      [ glClickAt (λ _ → ClickedAt) ] ...
  -- Draggable cylinder
  ∷ mesh (cylinder 0.5 1.5) (flat ...) [ glDrag (λ _ _ → Dragged) ] ...
  -- Focusable box (keyboard)
  ∷ mesh (box ...) (phong ...)
      (glFocusable ∷ glKeyDown (λ _ → KeyPressed) ∷ glScroll (λ _ → Scrolled) ∷ ...) ...
  -- Group: two spheres under common transform
  ∷ group (mkTransform ...) (mesh ... ∷ mesh ... ∷ [])
  -- Static + reactive text
  ∷ text3D "WebGL Full Demo" labelStyle [] ...
  ∷ bindText3D statsText infoStyle [] ...
  -- Icon
  ∷ icon (loadTexture "textures/info-icon.png") (vec2 0.5 0.5) [] ...
  ∷ [] )
```

**Key point:** `fromModel` makes camera reactive — projection, position, and target are all functions of model state. `bindLight` reactively updates light intensity. `onHover`/`onLeave` use color-picking for hover detection on 3D objects. `onClickAt` provides surface hit coordinates (Vec3). `onDrag` provides start+current Vec3 during drag. `focusable` + `onKeyDown` enable keyboard interaction on individual 3D objects. `text3D`/`bindText3D` render MSDF text in 3D space. `group` provides hierarchical transforms.

```bash
npm run build:webgl-full-demo
```

Source: `examples/WebGLFullDemo.agda`

---

## WebGL Controls Demo

**Demonstrates:** 3D UI controls from the `Agdelte.WebGL.Controls` library: themed buttons, toggle buttons, text labels.

```agda
open import Agdelte.WebGL.Controls

scene : Scene Model Msg
scene = mkScene
  (fixed (perspective 1.0 0.1 100.0) (vec3 0.0 1.0 5.0) (vec3 0.0 0.0 0.0))
  ( light (ambient white 0.4)
  ∷ light (directional white 0.7 (vec3 -0.5 -1.0 -0.3))
  -- Title
  ∷ text3D "WebGL Controls Demo"
      (mkTextStyle (builtin sans) 0.15 (rgb 0.2 0.5 0.9) center singleLine)
      []
      (mkTransform (vec3 0.0 1.5 0.0) identityQuat (vec3 1.0 1.0 1.0))
  -- Counter buttons
  ∷ button3D defaultTheme defaultButtonConfig "−"  Decrement
      (mkTransform (vec3 -1.0 0.7 0.0) identityQuat (vec3 1.0 1.0 1.0))
  ∷ button3D defaultTheme defaultButtonConfig "+"  Increment
      (mkTransform (vec3 1.0 0.7 0.0) identityQuat (vec3 1.0 1.0 1.0))
  -- Toggle buttons
  ∷ toggleButton defaultTheme defaultButtonConfig "Dark" darkMode ToggleDark
      (mkTransform (vec3 -1.5 0.0 0.0) identityQuat (vec3 1.0 1.0 1.0))
  -- Size variants
  ∷ smallButton3D defaultTheme "Small" Reset
      (mkTransform (vec3 -1.5 -0.7 0.0) identityQuat (vec3 1.0 1.0 1.0))
  ∷ defaultButton3D defaultTheme "Normal" Reset
      (mkTransform (vec3 0.0 -0.7 0.0) identityQuat (vec3 1.0 1.0 1.0))
  ∷ largeButton3D defaultTheme "Large" Reset
      (mkTransform (vec3 1.5 -0.7 0.0) identityQuat (vec3 1.0 1.0 1.0))
  ∷ [] )
```

**Key point:** `Agdelte.WebGL.Controls` provides a complete library of 3D UI components. `button3D`, `toggleButton`, `smallButton3D`, `largeButton3D`, `disabledButton` — all themed and interactive. Toggle buttons change color based on model state. The library includes buttons, sliders, toggles, menus, tabs, input fields, charts, audio visualizers, and gizmos.

```bash
npm run build:webgl-controls-demo
```

Source: `examples/WebGLControlsDemo.agda`

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
http://localhost:8080/examples_html/css-demo.html
http://localhost:8080/examples_html/css-full-demo.html
http://localhost:8080/examples_html/anim-demo.html
http://localhost:8080/examples_html/svg-test.html
http://localhost:8080/examples_html/svg-smil.html
http://localhost:8080/examples_html/svg-panzoom.html
http://localhost:8080/examples_html/svg-chart.html
http://localhost:8080/examples_html/svg-linedraw.html
http://localhost:8080/examples_html/webgl-test.html
http://localhost:8080/examples_html/webgl-full-demo.html
http://localhost:8080/examples_html/webgl-controls-demo.html

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
