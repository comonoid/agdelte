# Event (Subscriptions)

From `Agdelte.Core.Event`.

## Primitives

| Function | Type | Description |
|----------|------|-------------|
| `never` | `Event A` | No events |
| `interval` | `ℕ → A → Event A` | Tick every N ms |
| `timeout` | `ℕ → A → Event A` | Single event after N ms |

## Keyboard

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

### Keyboard Helpers

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

## WebSocket

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

## Routing

| Function | Type | Description |
|----------|------|-------------|
| `onUrlChange` | `(String → A) → Event A` | URL change (popstate) |

## Combinators

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

## Stateful Combinators

| Function | Type | Description |
|----------|------|-------------|
| `foldE` | `A → (B → A → A) → Event B → Event A` | Accumulate state across events |
| `mapFilterE` | `(B → Maybe A) → Event B → Event A` | Map + filter in one step |
| `switchE` | `Event A → Event (Event A) → Event A` | Dynamic event source switching |

## Derived Combinators

| Function | Type | Description |
|----------|------|-------------|
| `accumE` | `A → Event (A → A) → Event A` | Apply function events to accumulator |
| `mapAccum` | `(B → S → S × A) → S → Event B → Event A` | Map with state |
| `gate` | `(A → Bool) → Event A → Event A` | Synonym for filterE |
| `partitionE` | `(A → Bool) → Event A → Event A × Event A` | Split by predicate |
| `leftmost` | `List (Event A) → Event A` | Priority merge (= mergeAll in async) |

## Sequential / Monadic Combinators

| Function | Type | Description |
|----------|------|-------------|
| `occur` | `A → Event A` | Immediate one-shot event (= timeout 0) |
| `delay` | `ℕ → Event ⊤` | Delay N ms, fire unit |
| `_>>=E_` | `Event A → (A → Event B) → Event B` | Event bind via switchE |
| `sequenceE` | `List (Event A) → Event (List A)` | Sequential execution, collect results |

## Web Workers

| Function | Type | Description |
|----------|------|-------------|
| `worker` | `String → String → (String → A) → (String → A) → Event A` | Spawn worker (scriptUrl, input, onResult, onError) |
| `workerWithProgress` | `String → String → (String → A) → (String → A) → (String → A) → Event A` | Worker with progress protocol |

### Worker Message Protocol

**Simple worker** (`worker`): Worker should post a single result string.

```javascript
// worker.js
self.onmessage = (e) => {
  const result = compute(e.data);
  self.postMessage(result);  // Single response, worker can be reused
};
```

**Progress worker** (`workerWithProgress`): Worker posts progress updates, then final result.

```javascript
// worker-progress.js
self.onmessage = (e) => {
  for (let i = 0; i < 100; i++) {
    // Progress update (any string NOT starting with "done:")
    self.postMessage(`${i}%`);
  }
  // Final result (MUST start with "done:")
  self.postMessage("done:" + JSON.stringify(result));
};
```

## Worker Pools

| Function | Type | Description |
|----------|------|-------------|
| `poolWorker` | `ℕ → String → String → (String → A) → (String → A) → Event A` | Pool worker (poolSize, scriptUrl, input, onOk, onErr) |
| `poolWorkerWithProgress` | `ℕ → String → String → (String → A) → (String → A) → (String → A) → Event A` | Pool worker with progress |

### Pool Size Recommendations

| Use Case | Pool Size |
|----------|-----------|
| CPU-intensive | `navigator.hardwareConcurrency` (usually 4-8) |
| I/O-bound | 2-4× core count |
| Light tasks | 2-4 |

Pools auto-cleanup after 30 seconds of inactivity.

## Worker Channels

| Function | Type | Description |
|----------|------|-------------|
| `workerChannel` | `String → (String → A) → (String → A) → Event A` | Long-lived bidirectional worker (scriptUrl, onMsg, onErr) |

For long-running workers that send multiple messages. Use `channelSend` command to send messages back.

### Error Handling

Worker errors include detailed information:
- Error message
- Source file and line/column (when available)
- Stack trace (when available)

The `onError` callback receives a formatted string with all available details.

### Cancellation

All worker subscriptions return `unsubscribe()`. Calling it:
- Terminates the worker immediately (simple workers)
- Removes from pool queue if pending (pool workers)
- Does NOT wait for graceful shutdown

## Concurrency Combinators

| Function | Type | Description |
|----------|------|-------------|
| `parallel` | `∀ {B} → List (Event B) → (List B → A) → Event A` | Subscribe to all, collect results |
| `race` | `List (Event A) → Event A` | First to fire wins, cancel rest |
| `parallelAll` | `List (Event A) → Event (List A)` | Collect all results into list |
| `raceTimeout` | `ℕ → A → Event A → Event A` | Race with timeout fallback |

## SharedArrayBuffer (Advanced)

For high-performance worker communication with zero-copy memory sharing.

| Function | Type | Description |
|----------|------|-------------|
| `allocShared` | `ℕ → (SharedBuffer → A) → Event A` | Allocate shared buffer |
| `workerShared` | `SharedBuffer → String → String → (String → A) → (String → A) → Event A` | Worker with shared buffer access |

**Requires server headers:**
```
Cross-Origin-Opener-Policy: same-origin
Cross-Origin-Embedder-Policy: require-corp
```

Most apps should use regular `worker` / `workerWithProgress` instead — they work everywhere without special configuration.
