# Agdelte Examples Guide

All examples use **Reactive Bindings** (like Svelte) — no Virtual DOM.

## Overview

| Example | Features | Complexity |
|---------|----------|------------|
| [Counter](#counter) | Reactive bindings, onClick | Simple |
| [Timer](#timer) | Event subs (interval) | Simple |
| [Todo](#todo) | foreach, when, input | Medium |
| [KeyboardDemo](#keyboarddemo) | Global keyboard events, styleBind | Medium |
| [HttpDemo](#httpdemo) | Cmd (httpGet), disabledBind | Medium |
| [TaskDemo](#taskdemo) | Task chains, do-notation | Medium |
| [WebSocketDemo](#websocketdemo) | wsConnect, wsSend, foreach | Medium |
| [RouterDemo](#routerdemo) | SPA routing, when | Medium |
| [CompositionDemo](#compositiondemo) | focusNode, shared total | Advanced |

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

**Demonstrates:** `foreach` for dynamic lists, `when` for conditional rendering, input handling.

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
      [ foreach todos viewTodoItem ]   -- reactive list!
  ∷ when hasTodos (
      div [ class "footer" ] [ ... ]   -- conditional footer
    )
  ∷ [] )
```

**Key point:** `foreach` renders list items reactively. `when` conditionally shows/hides elements.

---

## KeyboardDemo

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

## HttpDemo

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

## TaskDemo

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

## WebSocketDemo

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

## RouterDemo

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

## CompositionDemo

**Demonstrates:** Two counters composed with shared total via `focusNode`.

```agda
-- Shared model
record Model : Set where
  field
    counter1 : ℕ
    counter2 : ℕ

-- Reuse counter template with focusNode
focusNode counter1 counterTemplate  -- maps Inner→Outer
focusNode counter2 counterTemplate

-- Shared total binding
bindF (λ m → show (counter1 m + counter2 m))
```

**Key point:** `focusNode` allows reusing templates with different model slices. Shared state via parent model.

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
http://localhost:8080/examples_html/composition.html
```

## Structure Pattern

Every example follows this pattern:

```agda
module Examples.MyExample where

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
