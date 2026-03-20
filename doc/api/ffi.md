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

### Crypto FFI (`FFI.Crypto`)

Haskell-only postulates (MAlonzo, via cryptonite/bcrypt):

| Function | Type | Description |
|----------|------|-------------|
| `hmacSHA256` | `String → String → String` | HMAC-SHA256 (secret × message → hex digest) |
| `hashPassword` | `String → IO String` | Bcrypt hash (cost 12) |
| `verifyPassword` | `String → String → Bool` | Verify password against bcrypt hash |
| `randomBytesB64` | `ℕ → IO String` | Generate N random bytes as base64 |
| `base64Encode` | `String → String` | Base64 encode |
| `base64Decode` | `String → String` | Base64 decode |

### File System FFI (`FFI.FileSystem`)

Haskell-only postulates (MAlonzo):

| Function | Type | Description |
|----------|------|-------------|
| `readFileText` | `String → IO String` | Read file as text |
| `writeFileText` | `String → String → IO ⊤` | Write text to file |
| `appendFileText` | `String → String → IO ⊤` | Append text to file |
| `doesFileExist'` | `String → IO Bool` | Check file existence |
| `mkdirp` | `String → IO ⊤` | Create directory recursively |
| `renameFile` | `String → String → IO ⊤` | Atomic rename |
| `readFileSafe` | `String → IO String` | Safe read (empty string if missing) |

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
