# Agdelte API Reference

## Core Types

### ReactiveApp

```agda
record ReactiveApp (Model Msg : Set) : Set₁ where
  field
    init     : Model
    update   : Msg → Model → Model
    template : Node Model Msg
```

### Constructor

```agda
mkReactiveApp : Model → (Msg → Model → Model) → Node Model Msg → ReactiveApp Model Msg
```

### Subscriptions and Commands (separate exports)

```agda
-- Exported separately from module:
subs : Model → Event Msg      -- optional
cmd  : Msg → Model → Cmd Msg  -- optional
```

---

## Node — Reactive Template

From `Agdelte.Reactive.Node`:

```agda
data Node (Model Msg : Set) : Set₁ where
  text         : String → Node Model Msg
  bind         : Binding Model String → Node Model Msg
  elem         : String → List (Attr Model Msg) → List (Node Model Msg) → Node Model Msg
  empty        : Node Model Msg
  when         : (Model → Bool) → Node Model Msg → Node Model Msg
  foreach      : ∀ {A} → (Model → List A) → (A → ℕ → Node Model Msg) → Node Model Msg
  foreachKeyed : ∀ {A} → (Model → List A) → (A → String) → (A → ℕ → Node Model Msg) → Node Model Msg
  whenT        : (Model → Bool) → Transition → Node Model Msg → Node Model Msg
```

### Transition (Phase 3)

```agda
record Transition : Set where
  constructor mkTransition
  field
    enterClass : String    -- CSS class on enter
    leaveClass : String    -- CSS class on leave
    duration   : ℕ         -- ms before DOM removal on leave
```

### Binding

```agda
record Binding (Model : Set) (A : Set) : Set where
  field
    extract : Model → A
    equals  : A → A → Bool
```

### Smart Constructors

```agda
-- Reactive text binding
bindF : (Model → String) → Node Model Msg

-- Elements
div, span, button, p, h1, h2, h3, ul, li,
input, label, nav, a, pre : List (Attr Model Msg) → List (Node Model Msg) → Node Model Msg
```

### Attr

```agda
data Attr (Model Msg : Set) : Set₁ where
  attr      : String → String → Attr Model Msg
  attrBind  : String → Binding Model String → Attr Model Msg
  on        : String → Msg → Attr Model Msg
  onValue   : String → (String → Msg) → Attr Model Msg
  style     : String → String → Attr Model Msg
  styleBind : String → Binding Model String → Attr Model Msg
```

### Attr Smart Constructors

| Function | Type | Description |
|----------|------|-------------|
| `onClick` | `Msg → Attr Model Msg` | Click handler |
| `onInput` | `(String → Msg) → Attr Model Msg` | Input value |
| `onKeyDown` | `(String → Msg) → Attr Model Msg` | Key press value |
| `onChange` | `(String → Msg) → Attr Model Msg` | Change value |
| `class` | `String → Attr Model Msg` | Static class |
| `classBind` | `(Model → String) → Attr Model Msg` | Reactive class |
| `id'` | `String → Attr Model Msg` | Element id |
| `value` | `String → Attr Model Msg` | Static value |
| `valueBind` | `(Model → String) → Attr Model Msg` | Reactive value |
| `placeholder` | `String → Attr Model Msg` | Placeholder |
| `type'` | `String → Attr Model Msg` | Input type |
| `href` | `String → Attr Model Msg` | Link href |
| `disabled` | `Attr Model Msg` | Disabled |
| `disabledBind` | `(Model → Bool) → Attr Model Msg` | Reactive disabled |
| `checked` | `Attr Model Msg` | Checked |
| `checkedBind` | `(Model → Bool) → Attr Model Msg` | Reactive checked |
| `keyAttr` | `String → Attr Model Msg` | data-key |
| `styles` | `String → String → Attr Model Msg` | Static style |
| `vmodel` | `(Model → String) → (String → Msg) → List (Attr Model Msg)` | Two-way binding (valueBind + onInput) |

### Component Composition (Phase 4)

```agda
zoomNode : (M → M') → (Msg' → Msg) → Node M' Msg' → Node M Msg
zoomAttr : (M → M') → (Msg' → Msg) → Attr M' Msg' → Attr M Msg
```

`zoomNode` maps both model AND messages — child components are fully reusable:

```agda
zoomNode proj₁ LeftMsg counterTemplate
zoomNode proj₂ RightMsg counterTemplate
```

---

## Lens (Phase 4)

From `Agdelte.Reactive.Lens`:

```agda
record Lens (Outer Inner : Set) : Set where
  constructor mkLens
  field
    get : Outer → Inner
    set : Inner → Outer → Outer
  modify : (Inner → Inner) → Outer → Outer
```

| Function | Type | Description |
|----------|------|-------------|
| `idLens` | `Lens A A` | Identity lens |
| `_∘L_` | `Lens B C → Lens A B → Lens A C` | Composition |
| `fstLens` | `Lens (A × B) A` | First of pair |
| `sndLens` | `Lens (A × B) B` | Second of pair |

---

## Event (Subscriptions)

### Primitives

| Function | Type | Description |
|----------|------|-------------|
| `never` | `Event A` | No events |
| `interval` | `ℕ → A → Event A` | Tick every N ms |
| `timeout` | `ℕ → A → Event A` | Single event after N ms |

### Keyboard

| Function | Type | Description |
|----------|------|-------------|
| `onKeyDown` | `(KeyboardEvent → Maybe A) → Event A` | Key press |
| `onKeyUp` | `(KeyboardEvent → Maybe A) → Event A` | Key release |

```agda
record KeyboardEvent : Set where
  field
    key, code : String
    ctrl, alt, shift, meta : Bool
```

#### Keyboard Helpers

| Function | Type | Description |
|----------|------|-------------|
| `onKey` | `String → A → Event A` | Single key |
| `onKeys` | `List (String × A) → Event A` | Multiple keys (one listener) |
| `onKeyWhen` | `(KeyboardEvent → Bool) → A → Event A` | Custom predicate |
| `onCtrlKey` | `String → A → Event A` | Ctrl+key |
| `onEnter` | `A → Event A` | Enter key |
| `onEscape` | `A → Event A` | Escape key |
| `onArrowUp/Down/Left/Right` | `A → Event A` | Arrow keys |
| `onKeyReleased` | `String → A → Event A` | Key release |

### WebSocket

| Function | Type | Description |
|----------|------|-------------|
| `wsConnect` | `String → (WsMsg → A) → Event A` | Connect to WebSocket |

```agda
data WsMsg : Set where
  WsConnected : WsMsg
  WsMessage   : String → WsMsg
  WsClosed    : WsMsg
  WsError     : String → WsMsg
```

### Routing

| Function | Type | Description |
|----------|------|-------------|
| `onUrlChange` | `(String → A) → Event A` | URL change (popstate) |

### Combinators

| Function | Type | Description |
|----------|------|-------------|
| `merge` | `Event A → Event A → Event A` | Combine events |
| `mapE` | `(A → B) → Event A → Event B` | Transform |
| `filterE` | `(A → Bool) → Event A → Event A` | Filter |
| `debounce` | `ℕ → Event A → Event A` | After N ms pause |
| `throttle` | `ℕ → Event A → Event A` | Max once per N ms |
| `mergeAll` | `List (Event A) → Event A` | Merge list |
| `_<\|>_` | `Event A → Event A → Event A` | Infix merge |
| `_<$>_` | `(A → B) → Event A → Event B` | Infix mapE |

### Stateful Combinators (Phase 5)

| Function | Type | Description |
|----------|------|-------------|
| `foldE` | `A → (B → A → A) → Event B → Event A` | Accumulate state across events |
| `mapFilterE` | `(B → Maybe A) → Event B → Event A` | Map + filter in one step |
| `switchE` | `Event A → Event (Event A) → Event A` | Dynamic event source switching |

### Derived Combinators (Phase 5)

| Function | Type | Description |
|----------|------|-------------|
| `accumE` | `A → Event (A → A) → Event A` | Apply function events to accumulator |
| `mapAccum` | `(B → S → S × A) → S → Event B → Event A` | Map with state |
| `gate` | `(A → Bool) → Event A → Event A` | Synonym for filterE |
| `partitionE` | `(A → Bool) → Event A → Event A × Event A` | Split by predicate |
| `leftmost` | `List (Event A) → Event A` | Priority merge (= mergeAll in async) |

### Sequential / Monadic Combinators

| Function | Type | Description |
|----------|------|-------------|
| `occur` | `A → Event A` | Immediate one-shot event (= timeout 0) |
| `delay` | `ℕ → Event ⊤` | Delay N ms, fire unit |
| `_>>=E_` | `Event A → (A → Event B) → Event B` | Event bind via switchE |
| `sequenceE` | `List (Event A) → Event (List A)` | Sequential execution, collect results |

### Web Workers (Phase 7)

| Function | Type | Description |
|----------|------|-------------|
| `worker` | `String → String → (String → A) → (String → A) → Event A` | Spawn worker (scriptUrl, input, onResult, onError) |
| `workerWithProgress` | `String → String → (String → A) → (String → A) → (String → A) → Event A` | Worker with progress protocol |

### Worker Pools

| Function | Type | Description |
|----------|------|-------------|
| `poolWorker` | `ℕ → String → String → (String → A) → (String → A) → Event A` | Pool worker (poolSize, scriptUrl, input, onOk, onErr) |
| `poolWorkerWithProgress` | `ℕ → String → String → (String → A) → (String → A) → (String → A) → Event A` | Pool worker with progress |

### Worker Channels

| Function | Type | Description |
|----------|------|-------------|
| `workerChannel` | `String → (String → A) → (String → A) → Event A` | Long-lived bidirectional worker (scriptUrl, onMsg, onErr) |

### Concurrency Combinators

| Function | Type | Description |
|----------|------|-------------|
| `parallel` | `∀ {B} → List (Event B) → (List B → A) → Event A` | Subscribe to all, collect results |
| `race` | `List (Event A) → Event A` | First to fire wins, cancel rest |
| `parallelAll` | `List (Event A) → Event (List A)` | Collect all results into list |
| `raceTimeout` | `ℕ → A → Event A → Event A` | Race with timeout fallback |

### SharedArrayBuffer

| Function | Type | Description |
|----------|------|-------------|
| `allocShared` | `ℕ → (SharedBuffer → A) → Event A` | Allocate shared buffer (requires COOP/COEP) |
| `workerShared` | `SharedBuffer → String → String → (String → A) → (String → A) → Event A` | Worker with shared buffer access |

---

## Optics (Phase 6)

From `Agdelte.Reactive.Optic`:

### Prism

```agda
record Prism (S A : Set) : Set where
  field
    match : S → Maybe A
    build : A → S

_∘P_ : Prism B C → Prism A B → Prism A C
```

### Traversal

```agda
record Traversal (S A : Set) : Set where
  field
    toList  : S → List A
    overAll : (A → A) → S → S
```

### Affine

```agda
record Affine (S A : Set) : Set where
  field
    preview : S → Maybe A
    set     : A → S → S

_∘A_ : Affine B C → Affine A B → Affine A C
ixList : ℕ → Affine (List A) A
lensToAffine : Lens S A → Affine S A
prismToAffine : Prism S A → Affine S A
```

### Unified Optic

```agda
record Optic (S A : Set) : Set where
  field
    peek : S → Maybe A
    over : (A → A) → S → S

_∘O_ : Optic B C → Optic A B → Optic A C
fromLens : Lens S A → Optic S A
fromPrism : Prism S A → Optic S A
fromAffine : Affine S A → Optic S A
fromTraversal : Traversal S A → Optic S A
```

### Message Routing

```agda
routeMsg : Prism Msg Msg' → Lens M M' → (Msg' → M' → M') → Msg → M → M
```

### Typed Component Composition

In `Agdelte.Reactive.Node`:

```agda
zoomNodeL : Lens M M' → Prism Msg Msg' → Node M' Msg' → Node M Msg
zoomAttrL : Lens M M' → Prism Msg Msg' → Attr M' Msg' → Attr M Msg
```

### ProcessOptic (Phase 7)

From `Agdelte.Reactive.ProcessOptic` — server-to-server optic over Unix sockets:

```agda
record ProcessOptic (A : Set) : Set where
  field
    socketPath : String
    {{serial}} : Serialize A
```

| Function | Type | Description |
|----------|------|-------------|
| `serveProcessOptic` | `ProcessOptic A → IO String → (String → IO String) → IO ⊤` | Expose agent on Unix socket |
| `connectProcessOptic` | `ProcessOptic A → IO IpcHandle` | Connect to remote agent |
| `peekProcess` | `IpcHandle → IO (TransportResult A)` | Read remote state |
| `stepProcessOptic` | `IpcHandle → String → IO (TransportResult String)` | Step remote agent |
| `peekOnce` | `ProcessOptic A → IO (TransportResult A)` | One-shot peek (connect + read + close) |
| `stepOnce` | `ProcessOptic A → String → IO (TransportResult String)` | One-shot step |

Protocol: `"peek"` → state, `"step:INPUT"` → new state (over Unix domain socket).

### RemoteOptic (Phase 7)

From `Agdelte.Reactive.RemoteOptic` — browser-to-server optic over HTTP:

```agda
record RemoteOptic (A : Set) : Set where
  field
    baseUrl    : String
    {{serial}} : Serialize A
```

| Function | Type | Description |
|----------|------|-------------|
| `queryRemote` | `RemoteOptic A → (TransportResult A → Msg) → (String → Msg) → Cmd Msg` | GET /state |
| `stepRemote` | `RemoteOptic A → String → (TransportResult A → Msg) → (String → Msg) → Cmd Msg` | POST /step |
| `queryRemoteRaw` | `String → (String → Msg) → (String → Msg) → Cmd Msg` | Raw string query |
| `stepRemoteRaw` | `String → String → (String → Msg) → (String → Msg) → Cmd Msg` | Raw string step |

---

## Agent (Phase 7)

From `Agdelte.Concurrent.Agent` — polynomial coalgebra for concurrent processes:

```agda
record Agent (S I O : Set) : Set where
  field
    state   : S
    observe : S → O
    step    : S → I → S
```

| Function | Type | Description |
|----------|------|-------------|
| `mkAgent` | `S → (S → O) → (S → I → S) → Agent S I O` | Create agent |
| `stepAgent` | `Agent S I O → I → Agent S I O × O` | Step and observe |
| `mapObserve` | `(O → O') → Agent S I O → Agent S I O'` | Map output |
| `mapInput` | `(I' → I) → Agent S I O → Agent S I' O` | Contravariant input map |

---

## Wiring — Agent Composition (Phase 7)

From `Agdelte.Concurrent.Wiring` — polynomial lens composition of agents.

### AgentLens

```agda
record AgentLens (I₁ O₁ I₂ O₂ : Set) : Set where
  field
    fwd : O₁ → O₂
    bwd : O₁ → I₂ → I₁

through : AgentLens I O I' O' → Agent S I O → Agent S I' O'
```

| Function | Type | Description |
|----------|------|-------------|
| `idAL` | `AgentLens I O I O` | Identity lens |
| `_∘AL_` | `AgentLens I₂ O₂ I' O' → AgentLens I₁ O₁ I₂ O₂ → AgentLens I₁ O₁ I' O'` | Compose lenses |
| `through` | `AgentLens I O I' O' → Agent S I O → Agent S I' O'` | Apply lens to agent |

### Combinators

| Function | Type | Linear Logic | Description |
|----------|------|-------------|-------------|
| `_>>>_` | `Agent S₁ I M → Agent S₂ M O → Agent (S₁ × S₂) I O` | ◁ | Pipeline |
| `_***_` | `Agent S₁ I₁ O₁ → Agent S₂ I₂ O₂ → Agent (S₁ × S₂) (I₁ × I₂) (O₁ × O₂)` | ⊗ | Parallel |
| `_&_` | `Agent S₁ I₁ O₁ → Agent S₂ I₂ O₂ → Agent (S₁ × S₂) (I₁ ⊎ I₂) (O₁ × O₂)` | & | External choice |
| `_⊕_` | `Agent S₁ I₁ O₁ → Agent S₂ I₂ O₂ → Agent (S₁ ⊎ S₂) (I₁ ⊎ I₂) (O₁ ⊎ O₂)` | ⊕ | Internal choice |
| `fanout` | `Agent S₁ I O₁ → Agent S₂ I O₂ → Agent (S₁ × S₂) I (O₁ × O₂)` | Δ | Fan-out |
| `loop` | `Agent S (I × O) O → Agent S I O` | trace | Feedback |
| `selectLeft` | `AgentLens (I₁ ⊎ I₂) (O₁ × O₂) I₁ O₁` | π₁ | Select left branch |
| `selectRight` | `AgentLens (I₁ ⊎ I₂) (O₁ × O₂) I₂ O₂` | π₂ | Select right branch |

### Utilities

| Function | Type | Description |
|----------|------|-------------|
| `mapI` | `(I' → I) → Agent S I O → Agent S I' O` | Contravariant input map |
| `mapO` | `(O → O') → Agent S I O → Agent S I O'` | Covariant output map |
| `remap` | `(I' → I) → (O → O') → Agent S I O → Agent S I' O'` | Both at once |
| `swap` | `Agent S (I₁ × I₂) O → Agent S (I₂ × I₁) O` | Swap inputs |
| `constAgent` | `O → Agent O I O` | Constant output |
| `terminal` | `Agent ⊤ I ⊤` | Unit agent |

### Existential wrapper

```agda
record SomeAgent (I O : Set) : Set₁ where
  field
    {State} : Set
    agent : Agent State I O

pack : Agent S I O → SomeAgent I O
_>>>ₛ_ _***ₛ_ _&ₛ_ _⊕ₛ_ -- compositions on packed agents
```

---

## Session Types (Phase 7)

From `Agdelte.Concurrent.Session` — typed communication protocols as sugar over polynomial lenses.

### Session

```agda
data Session : Set₁ where
  send   : (A : Set) → Session → Session   -- produce A, continue
  recv   : (A : Set) → Session → Session   -- consume A, continue
  offer  : Session → Session → Session      -- client picks branch (&)
  choose : Session → Session → Session      -- system picks branch (⊕)
  done   : Session                           -- protocol complete
```

### Duality

```agda
dual : Session → Session
-- send ↔ recv, offer ↔ choose, done ↔ done
```

### Interpretation

```agda
SessionI : Session → Set    -- input type for a session
SessionO : Session → Set    -- output type for a session
SessionAgent : Session → Set → Set
SessionAgent s S = Agent S (SessionI s) (SessionO s)
```

### Example protocols

```agda
ReqResp : Set → Set → Session
ReqResp Req Resp = recv Req (send Resp done)

ProcessProtocol : Session
ProcessProtocol = offer
  (recv ⊤ (send String done))       -- peek
  (recv String (send String done))   -- step
```

### Smart constructors

| Function | Type | Description |
|----------|------|-------------|
| `reqInput` | `Req → SessionI (ReqResp Req Resp)` | Pack request |
| `respOutput` | `SessionO (ReqResp Req Resp) → Resp` | Unpack response |
| `offerLeft` | `SessionI s₁ → SessionI (offer s₁ s₂)` | Select left branch |
| `offerRight` | `SessionI s₂ → SessionI (offer s₁ s₂)` | Select right branch |
| `peekLens` | `AgentLens ... (SessionI PeekProtocol) (SessionO PeekProtocol)` | Lens for peek |
| `stepLens` | `AgentLens ... (SessionI StepProtocol) (SessionO StepProtocol)` | Lens for step |

### Builders

```agda
mkReqResp : S → (S → Resp) → (S → Req → S) → SessionAgent (ReqResp Req Resp) S
mkOffer : SessionAgent s₁ S₁ → SessionAgent s₂ S₂ → SessionAgent (offer s₁ s₂) (S₁ × S₂)
```

---

## ProcessOpticLinear — Indexed IPC Handle (Phase 7)

From `Agdelte.Concurrent.ProcessOpticLinear` — type-safe IPC with connection state tracking.

```agda
data ConnState : Set where
  Connected Disconnected : ConnState

data IpcHandleL : ConnState → Set where
  mkHandle : IpcHandle → IpcHandleL Connected
```

| Function | Type | Description |
|----------|------|-------------|
| `connect` | `String → IO (IpcHandleL Connected)` | Connect to Unix socket |
| `query` | `IpcHandleL Connected → IO String` | Peek (only on Connected) |
| `step` | `IpcHandleL Connected → String → IO String` | Step (only on Connected) |
| `close` | `IpcHandleL Connected → IO ⊤` | Close (Connected → void) |
| `queryAndClose` | `String → IO String` | Safe one-shot peek |
| `stepAndClose` | `String → String → IO String` | Safe one-shot step |

Type-level guarantees:
- Cannot query after disconnect
- Cannot disconnect twice
- Only `Connected` handles can be used

---

## FFI (Phase 7)

### Shared Types (`FFI.Shared`)

```agda
record Serialize (A : Set) : Set where
  field
    encode : A → String
    decode : String → Maybe A

record Envelope : Set where
  field
    tag     : String
    payload : String

data TransportResult (A : Set) : Set where
  success : A → TransportResult A
  failure : String → TransportResult A
```

### Browser FFI (`FFI.Browser`)

Postulates for browser-specific primitives: `Element`, `SharedBuffer`, `TimerHandle`, DOM, clipboard, storage, URL/history.

### Server FFI (`FFI.Server`)

Haskell-only postulates via MAlonzo:

| Function | Description |
|----------|-------------|
| `putStrLn`, `getLine` | Basic IO |
| `_>>=_`, `_>>_`, `pure` | IO combinators |
| `IORef`, `newIORef`, `readIORef`, `writeIORef` | Mutable references |
| `listen` | HTTP server |
| `IpcHandle`, `serveAgentProcess`, `connectProcess`, `queryProcess`, `stepProcess`, `closeProcess` | Unix socket IPC |
| `mkAgentDef`, `runAgentServer1`, `runAgentServer2` | Multi-agent server + WebSocket |

---

## Testing (Phase 5)

From `Agdelte.Test.Interpret`:

```agda
SimEvent : Set → Set
SimEvent A = List (List A)   -- outer = ticks, inner = simultaneous events
```

| Function | Type | Description |
|----------|------|-------------|
| `simMapE` | `(A → B) → SimEvent A → SimEvent B` | Map |
| `simFilterE` | `(A → Bool) → SimEvent A → SimEvent A` | Filter |
| `simFoldE` | `A → (B → A → A) → SimEvent B → SimEvent A` | Fold |
| `simAccumE` | `A → SimEvent (A → A) → SimEvent A` | Accumulate |
| `simMerge` | `SimEvent A → SimEvent A → SimEvent A` | Merge |
| `simMapFilterE` | `(A → Maybe B) → SimEvent A → SimEvent B` | Map + filter |
| `interpretApp` | `(B → A → A) → A → SimEvent B → List A` | Test update logic |
| `collectN` | `ℕ → SimEvent A → SimEvent A` | Collect N ticks |

---

## Cmd (Commands)

### HTTP

| Function | Type | Description |
|----------|------|-------------|
| `httpGet` | `String → (String → A) → (String → A) → Cmd A` | GET request |
| `httpPost` | `String → String → (String → A) → (String → A) → Cmd A` | POST request |

### Task Integration

| Function | Type | Description |
|----------|------|-------------|
| `attempt` | `Task A → (Result String A → A) → Cmd A` | Run Task |

### DOM Effects

| Function | Type | Description |
|----------|------|-------------|
| `focus` | `String → Cmd A` | Focus element (CSS selector) |
| `blur` | `String → Cmd A` | Blur element |
| `scrollTo` | `ℕ → ℕ → Cmd A` | Scroll to position |
| `scrollIntoView` | `String → Cmd A` | Scroll element into view |

### Clipboard

| Function | Type | Description |
|----------|------|-------------|
| `writeClipboard` | `String → Cmd A` | Write to clipboard |
| `readClipboard` | `(String → A) → Cmd A` | Read from clipboard |

### LocalStorage

| Function | Type | Description |
|----------|------|-------------|
| `getItem` | `String → (Maybe String → A) → Cmd A` | Get item |
| `setItem` | `String → String → Cmd A` | Set item |
| `removeItem` | `String → Cmd A` | Remove item |

### WebSocket

| Function | Type | Description |
|----------|------|-------------|
| `wsSend` | `String → String → Cmd A` | Send message (url, message) |

### Worker Channels

| Function | Type | Description |
|----------|------|-------------|
| `channelSend` | `String → String → Cmd A` | Send to worker channel (scriptUrl, message) |

### Agent Interaction

| Function | Type | Description |
|----------|------|-------------|
| `agentQuery` | `String → (String → A) → (String → A) → Cmd A` | GET agent state |
| `agentStep` | `String → String → (String → A) → (String → A) → Cmd A` | POST step to agent |
| `agentStep!` | `String → (String → A) → (String → A) → Cmd A` | POST step (empty body) |

### Routing

| Function | Type | Description |
|----------|------|-------------|
| `pushUrl` | `String → Cmd A` | Push URL to history |
| `replaceUrl` | `String → Cmd A` | Replace current URL |
| `back` | `Cmd A` | Go back |
| `forward` | `Cmd A` | Go forward |

### Composition

| Function | Type | Description |
|----------|------|-------------|
| `ε` | `Cmd A` | Empty command |
| `_<>_` | `Cmd A → Cmd A → Cmd A` | Compose commands |
| `mapCmd` | `(A → B) → Cmd A → Cmd B` | Transform |

---

## Task (Monadic Chains)

```agda
data Task (A : Set) : Set where
  pure    : A → Task A
  fail    : String → Task A
  httpGet : String → (String → Task A) → (String → Task A) → Task A
  httpPost : String → String → (String → Task A) → (String → Task A) → Task A
```

### Monad Operations

```agda
_>>=_  : Task A → (A → Task B) → Task B
_>>_   : Task A → Task B → Task B
return : A → Task A
```

### Helpers

```agda
http : String → Task String                    -- GET, fail on error
httpPost′ : String → String → Task String      -- POST, fail on error
```

### Usage with do-notation

```agda
fetchData : Task UserData
fetchData = do
  token ← http "/api/token"
  user ← http ("/api/user?token=" ++ token)
  pure (parseUser user)

-- In command:
cmd Fetch _ = attempt fetchData GotResult
```
