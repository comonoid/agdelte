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

**Demonstrates:** `foreachKeyed` for keyed list reconciliation (Phase 3), `when` for conditional rendering, input handling.

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

**Demonstrates:** `whenT` with CSS enter/leave transitions (Phase 3). Auto-dismiss via `timeout`.

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

**Demonstrates:** Two counters composed with shared total via `zoomNode` (Phase 4).

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

**Demonstrates:** `foldE` + `mapFilterE` stateful event pipeline (Phase 5).

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

**Demonstrates:** Runtime optic composition with `ixList`, `Traversal`, `_∘O_`, `peek` (Phase 6 advanced).

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
