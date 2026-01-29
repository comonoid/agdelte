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
