# Agdelte Examples Guide

All examples follow Elm Architecture and demonstrate specific features.

## Overview

| Example | Features | Complexity |
|---------|----------|------------|
| [Counter](#counter) | Basic App, onClick | Simple |
| [Timer](#timer) | Event subs (interval) | Simple |
| [Todo](#todo) | Lists, input, filtering | Medium |
| [KeyboardDemo](#keyboarddemo) | Global keyboard events | Medium |
| [HttpDemo](#httpdemo) | Cmd (httpGet) | Medium |
| [TaskDemo](#taskdemo) | Task chains, do-notation | Medium |
| [WebSocketDemo](#websocketdemo) | wsConnect, wsSend | Medium |
| [RouterDemo](#routerdemo) | SPA routing, navLink | Medium |
| [CompositionDemo](#compositiondemo) | App composition (_∥_) | Advanced |

---

## Counter

**Demonstrates:** Basic Elm Architecture, button clicks.

```agda
data Msg = Inc | Dec

update : Msg → ℕ → ℕ
update Inc n = suc n
update Dec n = pred n

view : ℕ → Html Msg
view n = div []
  [ button [ onClick Dec ] [ text "-" ]
  , span [] [ text (show n) ]
  , button [ onClick Inc ] [ text "+" ]
  ]

app = simpleApp 0 update view
```

**Key point:** `simpleApp` for apps without subscriptions or commands.

---

## Timer

**Demonstrates:** Event subscriptions (interval).

```agda
data Msg = Tick | Toggle

record Model : Set where
  field
    seconds : ℕ
    running : Bool

subs : Model → Event Msg
subs m = if running m then interval 1000 Tick else never
```

**Key point:** `subs` returns different Event based on model state.

---

## Todo

**Demonstrates:** Lists, input handling, filtering.

```agda
data Filter = All | Active | Completed

record Todo : Set where
  field
    id        : ℕ
    text      : String
    completed : Bool

view : Model → Html Msg
view m = div []
  [ input [ onInput UpdateInput, value (inputText m) ] []
  , ul [] (map viewTodo (filterTodos (filter m) (todos m)))
  ]
```

**Key point:** Lists with `map`, conditional rendering with `when`.

---

## KeyboardDemo

**Demonstrates:** Global keyboard event handling.

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
```

**Key point:** `onKeyDown` with Maybe — filter keys at subscription level.

---

## HttpDemo

**Demonstrates:** HTTP requests via Cmd.

```agda
data Msg = Fetch | GotData String | GotError String

command : Msg → Model → Cmd Msg
command Fetch _ = httpGet "/api/data" GotData GotError
command _ _ = ε

update : Msg → Model → Model
update Fetch m = record m { status = Loading }
update (GotData d) m = record m { status = Ready d }
update (GotError e) m = record m { status = Error e }
```

**Key point:** `update` stays simple, HTTP logic in `command`.

---

## TaskDemo

**Demonstrates:** Sequential HTTP chains with do-notation.

```agda
fetchChain : Task String
fetchChain = do
  user ← http "/api/user"
  posts ← http ("/api/users/" ++ user ++ "/posts")
  pure (combine user posts)

command : Msg → Model → Cmd Msg
command Fetch _ = attempt fetchChain GotResult
command _ _ = ε
```

**Key point:** `Task` monad for sequential operations, `attempt` to run.

---

## WebSocketDemo

**Demonstrates:** WebSocket connection and messaging.

```agda
record Model : Set where
  field
    wantConnected : Bool   -- intent (for subscriptions)
    connected     : Bool   -- actual status
    messages      : List ChatMsg
    input         : String

subs : Model → Event Msg
subs m = if wantConnected m then wsConnect wsUrl WsEvent else never

command : Msg → Model → Cmd Msg
command Send m = if connected m
  then wsSend wsUrl (input m)
  else ε
command _ _ = ε
```

**Key point:** Separate `wantConnected` (intent) from `connected` (status) to prevent subscription cycling.

---

## RouterDemo

**Demonstrates:** SPA routing with browser history.

```agda
data Route = Home | About | Counter

subs : Model → Event Msg
subs _ = onUrlChange (Navigate ∘ parseRoute)

command : Msg → Model → Cmd Msg
command (Navigate r) _ = ε  -- No command needed, just update route
command _ _ = ε

view : Model → Html Msg
view m = div []
  [ nav []
      [ navLink' "/" (Navigate Home) "Home"
      , navLink' "/about" (Navigate About) "About"
      , navLink' "/counter" (Navigate Counter) "Counter"
      ]
  , viewRoute (route m)
  ]
```

**Key point:** `navLink` handles preventDefault automatically. Use `onUrlChange` for popstate events.

---

## CompositionDemo

**Demonstrates:** Parallel app composition.

```agda
-- Two counters running independently
twoCounters : App (ℕ × ℕ) (CounterMsg ⊎ CounterMsg)
twoCounters = counter ∥ counter

-- Custom view wrapping composed app
app = App.withView customView twoCounters
  where
    customView : (ℕ × ℕ) → Html (CounterMsg ⊎ CounterMsg)
    customView (l , r) = div []
      [ div [] [ text "Left: ", mapHtml inj₁ (counterView l) ]
      , div [] [ text "Right: ", mapHtml inj₂ (counterView r) ]
      ]
```

**Key point:** `_∥_` combines apps, `mapHtml` transforms messages, `withView` replaces view.

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
open import Agdelte.App
open import Agdelte.Core.Event
open import Agdelte.Core.Cmd
open import Agdelte.Html.Types
open import Agdelte.Html.Elements
open import Agdelte.Html.Events

-- 2. Model
record Model : Set where
  field ...

-- 3. Messages
data Msg : Set where ...

-- 4. Update (pure!)
update : Msg → Model → Model

-- 5. View (pure!)
view : Model → Html Msg

-- 6. Subscriptions
subs : Model → Event Msg

-- 7. Commands (if needed)
command : Msg → Model → Cmd Msg

-- 8. App
app : App Model Msg
app = mkApp init update view subs           -- simple
app = mkCmdApp init update view subs cmd    -- with commands
```
