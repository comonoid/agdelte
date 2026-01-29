# Agdelte Architecture

## Core Principle

**Svelte-style reactivity + Dependent types + No Virtual DOM**

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

## Reactive Templates (Svelte-style)

```agda
record ReactiveApp (Model Msg : Set) : Set₁ where
  field
    init     : Model                    -- initial state
    update   : Msg → Model → Model      -- pure state transition
    template : Node Model Msg           -- reactive template (NOT a function!)
```

### Key Insight: No Virtual DOM

| Virtual DOM (React/Elm) | Reactive Bindings (Svelte/Agdelte) |
|-------------------------|-------------------------------------|
| `view : Model → Html`   | `template : Node Model Msg`         |
| Rebuilds tree each time | Static structure with bindings      |
| Diff old vs new tree    | Check only bound values             |
| O(tree size) updates    | O(bindings) updates                 |

### How It Works

```
1. FIRST RENDER:
   - Walk Node tree, create real DOM
   - For each `bind`, remember (DOMNode, Binding)

2. ON MODEL CHANGE:
   - For each binding: oldValue vs newValue
   - If changed → update that DOM node directly
   - NO tree diffing!
```

This is exactly what Svelte does at compile time, but with explicit bindings.

## Event — Subscriptions

```agda
data Event (A : Set) : Set where
  never      : Event A
  interval   : ℕ → A → Event A
  timeout    : ℕ → A → Event A
  merge      : Event A → Event A → Event A
  onKeyDown  : (KeyboardEvent → Maybe A) → Event A
  onKeyUp    : (KeyboardEvent → Maybe A) → Event A
  wsConnect  : String → (WsMsg → A) → Event A
  onUrlChange : (String → A) → Event A
  debounce   : ℕ → Event A → Event A
  throttle   : ℕ → Event A → Event A
```

Events are **data** (AST), interpreted by runtime. This enables:
- Diffing subscriptions
- Automatic cleanup
- Fingerprint comparison (no unnecessary resubscription)

## Cmd — Commands

```agda
data Cmd (A : Set) : Set where
  ε            : Cmd A                    -- empty
  _<>_         : Cmd A → Cmd A → Cmd A    -- composition
  httpGet      : String → (String → A) → (String → A) → Cmd A
  httpPost     : String → String → (String → A) → (String → A) → Cmd A
  attempt      : Task A → (Result String A → A) → Cmd A
  -- DOM
  focus        : String → Cmd A
  blur         : String → Cmd A
  scrollTo     : ℕ → ℕ → Cmd A
  scrollIntoView : String → Cmd A
  -- Clipboard
  writeClipboard : String → Cmd A
  readClipboard  : (String → A) → Cmd A
  -- Storage
  getItem    : String → (Maybe String → A) → Cmd A
  setItem    : String → String → Cmd A
  removeItem : String → Cmd A
  -- WebSocket
  wsSend     : String → String → Cmd A
  -- Routing
  pushUrl    : String → Cmd A
  replaceUrl : String → Cmd A
  back       : Cmd A
  forward    : Cmd A
```

Commands are **executed once** when dispatched.

## Task — Monadic Chains

```agda
data Task (A : Set) : Set where
  pure    : A → Task A
  fail    : String → Task A
  httpGet : String → (String → Task A) → (String → Task A) → Task A
  httpPost : String → String → (String → Task A) → (String → Task A) → Task A

-- Monad instance enables do-notation
fetchChain : Task String
fetchChain = do
  user ← http "/api/user"
  posts ← http ("/api/users/" ++ userId user ++ "/posts")
  pure (format posts)

-- Run via attempt
command Fetch _ = attempt fetchChain GotResult
```

## App Composition

### Parallel Composition

```agda
_∥_ : App M₁ A₁ → App M₂ A₂ → App (M₁ × M₂) (A₁ ⊎ A₂)
```

Two apps run independently, model is a pair, messages are tagged.

### Component Composition (focusNode)

```agda
focusNode : (Outer → Inner) → Node Inner Msg → Node Outer Msg
focusBinding : (Outer → Inner) → Binding Inner A → Binding Outer A
```

This allows reusing templates with different model slices — similar to Svelte's component props but with type-safe lenses.

## Node — Reactive Template

```agda
data Node (Model Msg : Set) : Set₁ where
  text    : String → Node Model Msg                                                -- static text
  bind    : Binding Model String → Node Model Msg                                  -- reactive binding!
  elem    : String → List (Attr Model Msg) → List (Node Model Msg) → Node Model Msg
  empty   : Node Model Msg                                                         -- nothing
  when    : (Model → Bool) → Node Model Msg → Node Model Msg                      -- conditional
  foreach : ∀ {A} → (Model → List A) → (A → ℕ → Node Model Msg) → Node Model Msg -- dynamic list

data Attr (Model Msg : Set) : Set₁ where
  attr      : String → String → Attr Model Msg             -- static attribute
  attrBind  : String → Binding Model String → Attr Model Msg -- reactive attribute
  on        : String → Msg → Attr Model Msg                -- event handler
  onValue   : String → (String → Msg) → Attr Model Msg     -- event with value
  style     : String → String → Attr Model Msg
  styleBind : String → Binding Model String → Attr Model Msg

record Binding (Model : Set) (A : Set) : Set where
  field
    extract : Model → A           -- get value from model
    equals  : A → A → Bool        -- detect changes
```

### Smart Constructors

```agda
bindF : (Model → String) → Node Model Msg    -- most common: bindF show
onClick : Msg → Attr Model Msg               -- on "click"
onInput : (String → Msg) → Attr Model Msg    -- onValue "input"
class : String → Attr Model Msg              -- attr "class"
```

## Runtime Algorithm (No VDOM!)

```
1. model := app.init
2. Walk app.template, create real DOM
3. For each `bind`: remember (DOMNode, Binding)
4. Attach event handlers from `on` attributes
5. Subscribe to app.subs(model)
6. Wait for event (DOM click, interval, websocket, ...)
7. oldModel := model
8. model := app.update(msg, oldModel)
9. For each binding:
     oldVal := extract(oldModel)
     newVal := extract(model)
     if not equals(oldVal, newVal):
       update DOM node directly
10. goto 6
```

**Key difference from Virtual DOM**: No tree reconstruction, no diffing algorithm. O(bindings) instead of O(tree).

## Theoretical Foundation

In `Theory/` module (isolated, optional):

- **Poly** — Polynomial functors
- **Coalg** — Coalgebras (systems with state)
- **Lens** — Morphisms between Poly

Correspondences:
- `Signal A ≅ Coalg (Mono A ⊤)`
- `App ≅ Coalg (AppPoly) + init + events`
- `_∥_` corresponds to `⊗` on Poly level

This provides formal guarantees and enables future optimizations.

## Multi-Level Architecture

The architecture consists of three complementary levels:

```
┌─────────────────────────────────────────────────────────┐
│  Level 3: Declarative DSL                               │
│  button [ onClick Dec ] [ text "-" ]                   │
│  Aesthetic, readable, statically verified              │
└────────────────────────┬────────────────────────────────┘
                         │ compiles to / represented by
┌────────────────────────▼────────────────────────────────┐
│  Level 2: Lenses                                        │
│  focus : Lens Whole Part                               │
│  Navigation, modification, composition                  │
│  Dynamic flexibility at runtime                         │
└────────────────────────┬────────────────────────────────┘
                         │ based on
┌────────────────────────▼────────────────────────────────┐
│  Level 1: Polynomials                                   │
│  p(y) = Σ(i : I) y^(B i)                              │
│  Mathematical foundation                                │
└─────────────────────────────────────────────────────────┘
```

### Key Insight: Static Verification + Dynamic Flexibility

These levels are **not mutually exclusive** — they complement each other:

1. **Inductive types (DSL)** provide beautiful declarative syntax. Users write clean, readable code that the type checker verifies.

2. **Lenses** provide navigation and modification capabilities. They work *on* the structures defined by inductive types.

3. **Polynomials** provide the mathematical semantics that make everything composable and predictable.

### The "Big Lens" Principle

A lens can operate at any scale:
- **Small**: Navigate to a field in a record
- **Medium**: Transform a subtree of widgets
- **Large**: Restructure an entire network of widgets

```agda
-- Same abstraction at every scale:
fieldLens   : Lens Record Field
widgetLens  : Lens WidgetTree SubWidget
networkLens : Lens (Network Widget) (Network Widget')
```

This principle extends naturally to **concurrency**:
- Process = position in polynomial
- Channel = direction
- Lens = rerouting, transformation

### Static + Dynamic

The type system verifies the *initial* structure statically:

```agda
-- Type-checked at compile time:
myWidget : Widget Model Msg
myNetwork : Network Widget
```

But lenses allow *controlled* runtime modification:

```agda
-- At runtime, modify through lens (type-safe!):
modify networkLens restructure initialNetwork
```

This is the key: **well-typed programs don't go wrong, but can evolve**.

## Benefits

| Capability | Why It's Easy |
|------------|---------------|
| Time-travel debugging | Model is just data |
| Undo/Redo | List of previous Models |
| Serialization | `JSON.stringify(model)` |
| Testing | `update msg model ≡ expected` |
| Request cancellation | Automatic on unsubscribe |
| Race conditions | Impossible by construction |

## Comparison

| | Svelte 5 | Virtual DOM (React/Elm) | Agdelte |
|--|----------|-------------------------|---------|
| DOM updates | Direct (compiled) | Diff tree, patch | Direct (bindings) |
| Performance | Fast | Overhead from diffing | Fast |
| Reactivity | Compiler magic | Runtime diffing | Explicit bindings |
| Types | TypeScript | Varies | Dependent types |
| Template | `.svelte` file | `view : Model → Html` | `template : Node Model Msg` |
| Composition | Components | Components | Lenses + `_∥_` |
| Proofs | No | No | Yes (via Theory/) |
