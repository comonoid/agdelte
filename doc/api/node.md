# Node — Reactive Template

From `Agdelte.Reactive.Node`.

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

## Node

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

### Transition

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

---

## Attr

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

---

## Component Composition

```agda
zoomNode : (M → M') → (Msg' → Msg) → Node M' Msg' → Node M Msg
zoomAttr : (M → M') → (Msg' → Msg) → Attr M' Msg' → Attr M Msg
```

`zoomNode` maps both model AND messages — child components are fully reusable:

```agda
zoomNode proj₁ LeftMsg counterTemplate
zoomNode proj₂ RightMsg counterTemplate
```

## Lens

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
