# Cmd (Commands)

From `Agdelte.Core.Cmd`.

## HTTP

| Function | Type | Description |
|----------|------|-------------|
| `httpGet` | `String → (String → A) → (String → A) → Cmd A` | GET request |
| `httpPost` | `String → String → (String → A) → (String → A) → Cmd A` | POST request |
| `httpGetH` | `String → List (String × String) → (String → A) → (String → A) → Cmd A` | GET with custom headers |
| `httpPostH` | `String → List (String × String) → String → (String → A) → (String → A) → Cmd A` | POST with custom headers |

## Task Integration

| Function | Type | Description |
|----------|------|-------------|
| `attempt` | `Task A → (Result String A → A) → Cmd A` | Run Task |

## DOM Effects

| Function | Type | Description |
|----------|------|-------------|
| `focus` | `String → Cmd A` | Focus element (CSS selector) |
| `blur` | `String → Cmd A` | Blur element |
| `scrollTo` | `ℕ → ℕ → Cmd A` | Scroll to position |
| `scrollIntoView` | `String → Cmd A` | Scroll element into view |
| `callMethod` | `String → String → Cmd A` | Call method on element (selector, method) |
| `setProp` | `String → String → String → Cmd A` | Set property on element |
| `getProp` | `String → String → (String → A) → Cmd A` | Read property from element |

## MediaSource (Video)

| Function | Type | Description |
|----------|------|-------------|
| `mediaSourceInit` | `String → String → A → (String → A) → Cmd A` | Init MediaSource (selector, mimeType, onReady, onError) |
| `mediaSourceAppend` | `String → String → A → (String → A) → Cmd A` | Append segment (selector, base64, onDone, onError) |
| `mediaSourceEnd` | `String → Cmd A` | Signal end of stream |

## Clipboard

| Function | Type | Description |
|----------|------|-------------|
| `writeClipboard` | `String → Cmd A` | Write to clipboard |
| `readClipboard` | `(String → A) → Cmd A` | Read from clipboard |

## LocalStorage

| Function | Type | Description |
|----------|------|-------------|
| `getItem` | `String → (Maybe String → A) → Cmd A` | Get item |
| `setItem` | `String → String → Cmd A` | Set item |
| `removeItem` | `String → Cmd A` | Remove item |

## WebSocket

| Function | Type | Description |
|----------|------|-------------|
| `wsSend` | `String → String → Cmd A` | Send message (url, message) |

## Worker Channels

| Function | Type | Description |
|----------|------|-------------|
| `channelSend` | `String → String → Cmd A` | Send to worker channel (scriptUrl, message) |

## Agent Interaction

| Function | Type | Description |
|----------|------|-------------|
| `agentQuery` | `String → (String → A) → (String → A) → Cmd A` | GET agent state |
| `agentStep` | `String → String → (String → A) → (String → A) → Cmd A` | POST step to agent |
| `agentStep!` | `String → (String → A) → (String → A) → Cmd A` | POST step (empty body) |

## Routing

| Function | Type | Description |
|----------|------|-------------|
| `pushUrl` | `String → Cmd A` | Push URL to history |
| `replaceUrl` | `String → Cmd A` | Replace current URL |
| `back` | `Cmd A` | Go back |
| `forward` | `Cmd A` | Go forward |

## Composition

| Function | Type | Description |
|----------|------|-------------|
| `ε` | `Cmd A` | Empty command |
| `_<>_` | `Cmd A → Cmd A → Cmd A` | Compose commands |
| `mapCmd` | `(A → B) → Cmd A → Cmd B` | Transform |
