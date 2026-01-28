# Agdelte Architecture

## Core Principle

**Simple definitions + Isolated theory**

```
┌─────────────────────────────────────────────────────────────┐
│  USER LAYER                                                  │
│  Simple record definitions                                   │
│  App { init, update, view, subs, command }                  │
│  Clear error messages                                        │
├─────────────────────────────────────────────────────────────┤
│  LIBRARY LAYER                                               │
│  Typed combinators                                           │
│  mapE, merge, _∥_, mapMsg, mapCmd, withView                 │
├─────────────────────────────────────────────────────────────┤
│  THEORY LAYER (Theory/)                                      │
│  Poly, Coalg, Lens — formal foundations                     │
│  Proofs: Signal ≅ Coalg, App ≅ Coalg                        │
│  (isolated, imported on demand)                             │
└─────────────────────────────────────────────────────────────┘
```

## Elm Architecture with Explicit Effects

```agda
record App (Model Msg : Set) : Set where
  field
    init    : Model                    -- initial state
    update  : Msg → Model → Model      -- pure state transition
    view    : Model → Html Msg         -- pure rendering
    subs    : Model → Event Msg        -- subscriptions (continuous)
    command : Msg → Model → Cmd Msg    -- one-shot effects
```

### Key Separation

| Concept | Type | Purpose | Example |
|---------|------|---------|---------|
| `Event` | `subs` | Continuous subscriptions | interval, keyboard, websocket |
| `Cmd` | `command` | One-shot effects | HTTP, focus, clipboard |
| `Task` | in `Cmd` | Monadic chains | Sequential HTTP |

### Why This Separation?

**`update` stays simple**: `Msg → Model → Model`

Effects are handled separately:
- `subs` — what to listen to (declarative)
- `command` — what to do in response (imperative, but typed)

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

### Modifiers

```agda
withView   : (Model → Html Msg) → App Model Msg → App Model Msg
withUpdate : (Msg → Model → Model) → App Model Msg → App Model Msg
withSubs   : (Model → Event Msg) → App Model Msg → App Model Msg
withEvents : (Model → Event Msg) → App Model Msg → App Model Msg  -- merge
withCommand : (Msg → Model → Cmd Msg) → App Model Msg → App Model Msg  -- merge
```

### Message/Model Transformation

```agda
mapMsg   : (A → B) → (B → A) → App Model A → App Model B
mapModel : (M₂ → M₁) → (M₁ → M₂ → M₂) → M₂ → App M₁ Msg → App M₂ Msg
```

## Html

Type-safe virtual DOM:

```agda
data Html (Msg : Set) : Set where
  node  : String → List (Attr Msg) → List (Html Msg) → Html Msg
  text  : String → Html Msg
  keyed : String → List (Attr Msg) → List (String × Html Msg) → Html Msg

data Attr (Msg : Set) : Set where
  attr      : String → String → Attr Msg
  boolAttr  : String → Attr Msg
  style     : String → String → Attr Msg
  on        : String → Msg → Attr Msg
  onPrevent : String → Msg → Attr Msg  -- with preventDefault
  onInput   : (String → Msg) → Attr Msg
  onKey     : String → (String → Msg) → Attr Msg
  key       : String → Attr Msg
```

### Navigation

```agda
-- High-level navigation (from Agdelte.Html.Navigation)
navLink : String → Msg → List (Attr Msg) → List (Html Msg) → Html Msg
```

Automatically handles `preventDefault` for SPA navigation.

## Runtime Algorithm

```
1. model := app.init
2. html := app.view(model)
3. Render DOM, attach handlers
4. Subscribe to app.subs(model)
5. Wait for event (DOM, interval, websocket, ...)
6. cmd := app.command(msg, model)
7. model := app.update(msg, model)
8. Execute cmd
9. newSubs := app.subs(model)
10. if fingerprint(newSubs) ≠ fingerprint(oldSubs):
      unsubscribe(oldSubs)
      subscribe(newSubs)
11. Patch DOM with diff(oldHtml, app.view(model))
12. goto 5
```

Key optimization: **fingerprint comparison** for subscriptions prevents unnecessary unsubscribe/resubscribe cycles (critical for WebSocket).

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

| | Svelte 5 | Elm | Agdelte |
|--|----------|-----|---------|
| Reactivity | Compiler magic | Architecture | Elm-like + Poly theory |
| Types | TypeScript | ML | Dependent types |
| Effects | Hidden in $effect | Cmd (opaque) | Event (subs) + Cmd (explicit) |
| update | Mutations | Model × Cmd | Model (simple!) |
| Composition | Components | Boilerplate | `_∥_`, `mapMsg` (Poly inside) |
| Error messages | Good | Good | Good (simple types) |
| Proofs | No | No | Possible (via Theory/) |
