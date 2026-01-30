# FFI

## Shared Types (`FFI.Shared`)

```agda
record Serialize (A : Set) : Set where
  field
    encode : A → String
    decode : String → Maybe A

record Envelope : Set where
  field
    tag     : String
    payload : String

data TransportResult (A : Set) : Set where
  success : A → TransportResult A
  failure : String → TransportResult A
```

## Browser FFI (`FFI.Browser`)

Postulates for browser-specific primitives: `Element`, `SharedBuffer`, `TimerHandle`, DOM, clipboard, storage, URL/history.

## Server FFI (`FFI.Server`)

Haskell-only postulates via MAlonzo:

| Function | Description |
|----------|-------------|
| `putStrLn`, `getLine` | Basic IO |
| `_>>=_`, `_>>_`, `pure` | IO combinators |
| `IORef`, `newIORef`, `readIORef`, `writeIORef` | Mutable references |
| `listen` | HTTP server |
| `IpcHandle`, `serveAgentProcess`, `connectProcess`, `queryProcess`, `stepProcess`, `closeProcess` | Unix socket IPC |
| `mkAgentDef`, `runAgentServer1`, `runAgentServer2` | Multi-agent server + WebSocket |

## Testing (`Test.Interpret`)

```agda
SimEvent : Set → Set
SimEvent A = List (List A)   -- outer = ticks, inner = simultaneous events
```

| Function | Type | Description |
|----------|------|-------------|
| `simMapE` | `(A → B) → SimEvent A → SimEvent B` | Map |
| `simFilterE` | `(A → Bool) → SimEvent A → SimEvent A` | Filter |
| `simFoldE` | `A → (B → A → A) → SimEvent B → SimEvent A` | Fold |
| `simAccumE` | `A → SimEvent (A → A) → SimEvent A` | Accumulate |
| `simMerge` | `SimEvent A → SimEvent A → SimEvent A` | Merge |
| `simMapFilterE` | `(A → Maybe B) → SimEvent A → SimEvent B` | Map + filter |
| `interpretApp` | `(B → A → A) → A → SimEvent B → List A` | Test update logic |
| `collectN` | `ℕ → SimEvent A → SimEvent A` | Collect N ticks |
