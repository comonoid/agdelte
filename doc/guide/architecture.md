# Agdelte Architecture

## The Principle

The foundation is the most general thing: **polynomial functors** and **dependent lenses**. Every practical abstraction — `Lens`, `ReactiveApp`, `Agent`, `Session` — is a convenient special case with a proven isomorphism back to the general theory.

```
                    You write this
                         │
                         ▼
Level 3    DSL           button [ onClick Dec ] [ bindF show ]
Level 2    Lenses        Lens { get; set }, Optic, zoomNode
Level 1    Polynomials   Poly { Pos; Dir }, Coalg, Poly.Lens
                         ▲
                         │
                    This proves it composes
```

Level 1 is invisible unless you want it. Level 3 is all you need for apps. The isomorphisms connecting them live in `Theory/` and type-check to `refl`.

## Reactive Templates (No Virtual DOM)

```agda
record ReactiveApp (Model Msg : Set) : Set₁ where
  field
    init     : Model
    update   : Msg → Model → Model
    template : Node Model Msg    -- data, NOT a function
```

`template` is a static tree with `bind` points. This is the key difference from Virtual DOM frameworks:

| Virtual DOM (React/Elm) | Reactive Bindings (Svelte/Agdelte) |
|---|---|
| `view : Model → Html` | `template : Node Model Msg` |
| Rebuilds tree each time | Static structure with bindings |
| Diff old vs new tree | Check only bound values |
| O(tree size) | O(bindings) |

### Runtime Algorithm

```
1. Walk template → create real DOM → remember (DOMNode, Binding) pairs
2. On event: model' = update msg model
3. For each binding: if extract(model) ≠ extract(model') → update DOM node
4. No tree diffing. Ever.
```

### Polynomial Interpretation

`ReactiveApp M Msg ≅ Coalg(y^Msg)` — an app is a coalgebra of the polynomial `y^Msg`. The `update` function is the coalgebra structure map. Composition `_∥_` corresponds to the product of polynomials. Proof: `PolyApp.agda`.

## Node — The Template Language

```agda
data Node (Model Msg : Set) : Set₁ where
  text         : String → Node Model Msg
  bind         : Binding Model String → Node Model Msg             -- reactive!
  elem         : String → List (Attr) → List (Node) → Node
  when         : (Model → Bool) → Node → Node                     -- conditional
  foreach      : (Model → List A) → (A → ℕ → Node) → Node        -- lists
  foreachKeyed : (Model → List A) → (A → String) → (A → ℕ → Node) → Node
  whenT        : (Model → Bool) → Transition → Node → Node        -- animated

record Binding (Model A : Set) : Set where
  field
    extract : Model → A
    equals  : A → A → Bool
```

Smart constructors: `bindF show`, `onClick msg`, `onInput f`, `class "x"`.

## Lenses & Optics

```agda
record Lens (Outer Inner : Set) : Set where
  field
    get : Outer → Inner
    set : Inner → Outer → Outer

_∘L_ : Lens B C → Lens A B → Lens A C
```

This is `Poly.Lens (Mono S S) (Mono A A)` in disguise. The isomorphism is proved with round-trip `refl` in `OpticPolyLens.agda`.

The optics hierarchy: `Lens`, `Prism`, `Affine`, `Traversal`, unified as `Optic` with `_∘O_`.

### Component Composition

```agda
-- Raw functions
zoomNode : (M → M') → (Msg' → Msg) → Node M' Msg' → Node M Msg

-- Typed optics
zoomNodeL : Lens M M' → Prism Msg Msg' → Node M' Msg' → Node M Msg

-- Automatic message routing
routeMsg : Prism Msg Msg' → Lens M M' → ... → ...
```

## Effects

### Event — Subscriptions (declarative, diffable)

```agda
data Event (A : Set) : Set where
  never interval timeout onKeyDown onKeyUp
  httpGet httpPost wsConnect onUrlChange
  merge debounce throttle
  foldE mapFilterE switchE
  worker parallel race
```

Events are AST data. The runtime interprets them, fingerprints them for diffing, auto-cleans on unsubscribe. Stateful combinators (`foldE`, `switchE`) have runtime-managed internal state.

### Cmd — One-shot effects

HTTP, DOM manipulation, clipboard, storage, routing, WebSocket sends.

### Task — Monadic chains

```agda
fetchChain = do
  user  ← http "/api/user"
  posts ← http ("/api/users/" ++ userId user ++ "/posts")
  pure (format posts)
```

## Concurrency

### Agents as Polynomial Coalgebras

```agda
record Agent (S I O : Set) : Set where
  field
    state   : S
    observe : S → O       -- position
    step    : S → I → S   -- direction
```

This is `Coalg (Mono O I)`. The isomorphism is `refl` (proved in `AgentCoalg.agda`).

`AgentLens I₁ O₁ I₂ O₂` is literally a type alias for `Poly.Lens (Mono O₁ I₁) (Mono O₂ I₂)`. Not an isomorphism — identity.

### Wiring Combinators

| Combinator | Linear Logic | Polynomial operation |
|---|---|---|
| `_>>>_` | ◁ | Sequential pipeline |
| `_***_` | ⊗ | Parallel |
| `_&_` | & | External choice |
| `_⊕_` | ⊕ | Internal choice |
| `fanout` | Δ | Diagonal |
| `loop` | trace | Feedback |

### Session Types

```agda
data Session : Set₁ where
  send recv : (A : Set) → Session → Session
  offer choose : Session → Session → Session
  done : Session
```

Sessions compile to agent interfaces via `SessionI`/`SessionO`. Duality (`send ↔ recv`, `offer ↔ choose`) is proved involutive: `dual (dual s) ≡ s`.

### The Big Lens

Same `peek`/`over` interface at every scale:

| Scale | Module | Transport |
|---|---|---|
| Record field | `Reactive.Lens` | Direct |
| Component | `Reactive.Optic` | Direct |
| Process | `Reactive.ProcessOptic` | Unix socket / pipe |
| Network | `Reactive.RemoteOptic` | WebSocket |
| Anything | `Reactive.BigLens` | Polymorphic |

All are polynomial lenses. `BigLensPolyLens.agda` proves composition is preserved across the transport boundary.

## Isomorphism Table

| What | Is really | Where proved |
|---|---|---|
| `Lens S A` | `Poly.Lens (Mono S S) (Mono A A)` | `Theory/OpticPolyLens` |
| `ReactiveApp` | `Coalg (AppPoly) + init + events` | `Theory/PolyApp` |
| `Signal A` | `Coalg (Mono A ⊤)` | `Theory/PolySignal` |
| `Agent S I O` | `Coalg (Mono O I)` | `Theory/AgentCoalg` |
| `AgentLens` | `Poly.Lens` | Identity (type alias) |
| `BigLens` | `Coalg (Mono O I)` | `Theory/BigLensPolyLens` |
| `Lens ∘L` laws | Category laws | `Theory/LensLaws` |
| `dual ∘ dual = id` | Involution | `Theory/SessionDualProof` |

## Benefits

| Capability | Why |
|---|---|
| Time-travel debugging | Model is data |
| Undo/Redo | List of models |
| Serialization | `JSON.stringify(model)` |
| Testing | `update msg model ≡ expected` |
| Automatic cleanup | Event diffing |
| No race conditions | By construction |
| Correct composition | By polynomial theory |
