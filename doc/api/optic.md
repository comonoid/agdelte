# Optics

From `Agdelte.Reactive.Optic`.

## Prism

```agda
record Prism (S A : Set) : Set where
  field
    match : S → Maybe A
    build : A → S

_∘P_ : Prism B C → Prism A B → Prism A C
```

## Traversal

```agda
record Traversal (S A : Set) : Set where
  field
    toList  : S → List A
    overAll : (A → A) → S → S
```

## Affine

```agda
record Affine (S A : Set) : Set where
  field
    preview : S → Maybe A
    set     : A → S → S

_∘A_ : Affine B C → Affine A B → Affine A C
ixList : ℕ → Affine (List A) A
lensToAffine : Lens S A → Affine S A
prismToAffine : Prism S A → Affine S A
```

## Unified Optic

```agda
record Optic (S A : Set) : Set where
  field
    peek : S → Maybe A
    over : (A → A) → S → S

_∘O_ : Optic B C → Optic A B → Optic A C
fromLens : Lens S A → Optic S A
fromPrism : Prism S A → Optic S A
fromAffine : Affine S A → Optic S A
fromTraversal : Traversal S A → Optic S A
```

## Message Routing

```agda
routeMsg : Prism Msg Msg' → Lens M M' → (Msg' → M' → M') → Msg → M → M
```

## Typed Component Composition

In `Agdelte.Reactive.Node`:

```agda
zoomNodeL : Lens M M' → Prism Msg Msg' → Node M' Msg' → Node M Msg
zoomAttrL : Lens M M' → Prism Msg Msg' → Attr M' Msg' → Attr M Msg
```

## ProcessOptic

From `Agdelte.Reactive.ProcessOptic` — server-to-server optic over Unix sockets:

```agda
record ProcessOptic (A : Set) : Set where
  field
    socketPath : String
    {{serial}} : Serialize A
```

| Function | Type | Description |
|----------|------|-------------|
| `serveProcessOptic` | `ProcessOptic A → IO String → (String → IO String) → IO ⊤` | Expose agent on Unix socket |
| `connectProcessOptic` | `ProcessOptic A → IO IpcHandle` | Connect to remote agent |
| `peekProcess` | `IpcHandle → IO (TransportResult A)` | Read remote state |
| `stepProcessOptic` | `IpcHandle → String → IO (TransportResult String)` | Step remote agent |
| `peekOnce` | `ProcessOptic A → IO (TransportResult A)` | One-shot peek (connect + read + close) |
| `stepOnce` | `ProcessOptic A → String → IO (TransportResult String)` | One-shot step |

Protocol: `"peek"` → state, `"step:INPUT"` → new state (over Unix domain socket).

## RemoteOptic

From `Agdelte.Reactive.RemoteOptic` — browser-to-server optic over HTTP:

```agda
record RemoteOptic (A : Set) : Set where
  field
    baseUrl    : String
    {{serial}} : Serialize A
```

| Function | Type | Description |
|----------|------|-------------|
| `queryRemote` | `RemoteOptic A → (TransportResult A → Msg) → (String → Msg) → Cmd Msg` | GET /state |
| `stepRemote` | `RemoteOptic A → String → (TransportResult A → Msg) → (String → Msg) → Cmd Msg` | POST /step |
| `queryRemoteRaw` | `String → (String → Msg) → (String → Msg) → Cmd Msg` | Raw string query |
| `stepRemoteRaw` | `String → String → (String → Msg) → (String → Msg) → Cmd Msg` | Raw string step |

## Big Lens (IOOptic)

From `Agdelte.Reactive.BigLens` — network-wide optic, same peek/over interface across local widgets, server agents, and browser clients.

### IOOptic

```agda
record IOOptic : Set where
  constructor mkIOOptic
  field
    ioPeek : IO (Maybe String)    -- read remote state
    ioOver : String → IO String   -- send input, get result
```

### Constructors

```agda
processAgentOptic : String → IOOptic    -- Unix socket
refOptic : IORef String → IOOptic       -- Local IORef (testing)
constIOOptic : String → IOOptic         -- Constant (testing)
```

### Composition

```agda
_∘IO_ : IOOptic → IOOptic → IOOptic    -- sequential composition
```

## ProcessOpticLinear — Indexed IPC Handle

From `Agdelte.Concurrent.ProcessOpticLinear` — type-safe IPC with connection state tracking.

```agda
data ConnState : Set where
  Connected Disconnected : ConnState

data IpcHandleL : ConnState → Set where
  mkHandle : IpcHandle → IpcHandleL Connected
```

| Function | Type | Description |
|----------|------|-------------|
| `connect` | `String → IO (IpcHandleL Connected)` | Connect to Unix socket |
| `query` | `IpcHandleL Connected → IO String` | Peek (only on Connected) |
| `step` | `IpcHandleL Connected → String → IO String` | Step (only on Connected) |
| `close` | `IpcHandleL Connected → IO ⊤` | Close (Connected → void) |
| `queryAndClose` | `String → IO String` | Safe one-shot peek |
| `stepAndClose` | `String → String → IO String` | Safe one-shot step |

Type-level guarantees:
- Cannot query after disconnect
- Cannot disconnect twice
- Only `Connected` handles can be used
