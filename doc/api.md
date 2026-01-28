# Agdelte API Reference

## Core Types

### App

```agda
record App (Model Msg : Set) : Set where
  field
    init    : Model
    update  : Msg → Model → Model
    view    : Model → Html Msg
    subs    : Model → Event Msg
    command : Msg → Model → Cmd Msg
```

### Constructors

```agda
mkApp : Model → (Msg → Model → Model) → (Model → Html Msg)
      → (Model → Event Msg) → App Model Msg

mkCmdApp : Model → (Msg → Model → Model) → (Model → Html Msg)
         → (Model → Event Msg) → (Msg → Model → Cmd Msg) → App Model Msg

simpleApp : Model → (Msg → Model → Model) → (Model → Html Msg) → App Model Msg
```

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
command Fetch _ = attempt fetchData GotResult
```

---

## Html

### Elements

From `Agdelte.Html.Elements`:

```agda
div, span, p, h1, h2, h3, h4, h5, h6,
a, button, input, textarea, select, option,
ul, ol, li, table, tr, td, th,
form, label, img, br, hr, pre, code,
header, footer, main', nav, section, article, aside
```

### Attributes

From `Agdelte.Html.Attributes`:

```agda
-- Common
id, class, style', title, hidden

-- Links
href, src, alt

-- Forms
type', name, value, placeholder, disabled, readonly, checked, selected,
autofocus, required, min, max, step, pattern', maxlength, minlength,
rows, cols, wrap, multiple, accept, autocomplete, for'

-- Data
dataAttr  -- data-* attributes
```

### Events

From `Agdelte.Html.Events`:

```agda
-- Mouse
onClick, onDoubleClick, onMouseDown, onMouseUp,
onMouseEnter, onMouseLeave, onContextMenu

-- Keyboard
onKeyDown, onKeyUp, onKeyPress

-- Form
onInput', onChange, onSubmit, onFocus, onBlur

-- With preventDefault
onClickPrevent, onSubmitPrevent
```

### Navigation

From `Agdelte.Html.Navigation`:

```agda
navLink : String → Msg → List (Attr Msg) → List (Html Msg) → Html Msg
navLink' : String → Msg → String → Html Msg
navLinkClass : String → Msg → String → String → Html Msg
```

### Utilities

```agda
empty    : Html Msg                      -- empty text node
fragment : List (Html Msg) → Html Msg    -- wrapper div
when     : Bool → Html Msg → Html Msg    -- conditional
unless   : Bool → Html Msg → Html Msg    -- inverse conditional
mapHtml  : (A → B) → Html A → Html B     -- transform messages
```

---

## App Composition

### Parallel

```agda
_∥_ : App M₁ A₁ → App M₂ A₂ → App (M₁ × M₂) (A₁ ⊎ A₂)
tensor : App M₁ A₁ → App M₂ A₂ → App (M₁ × M₂) (A₁ ⊎ A₂)  -- alias
```

### Alternative

```agda
_⊕ᵃ_ : App M₁ A₁ → App M₂ A₂ → App (M₁ ⊎ M₂) (A₁ ⊎ A₂)
coproduct : ...  -- alias
```

### Modifiers

```agda
withView    : (Model → Html Msg) → App → App
withUpdate  : (Msg → Model → Model) → App → App
withSubs    : (Model → Event Msg) → App → App
withEvents  : (Model → Event Msg) → App → App  -- merge with existing
withCommand : (Msg → Model → Cmd Msg) → App → App  -- merge with existing
```

### Transformations

```agda
mapMsg   : (A → B) → (B → A) → App M A → App M B
mapModel : (M₂ → M₁) → (M₁ → M₂ → M₂) → M₂ → App M₁ Msg → App M₂ Msg
```

### Lifecycle

```agda
step  : Msg → App → App              -- apply one message
steps : List Msg → App → App         -- apply multiple messages
```
