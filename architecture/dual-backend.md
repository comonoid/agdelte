# Dual-Backend Architecture: JS (Browser) + Haskell (Server)

> **Status:** Planned (Phase 7). Architecture decision for client-server split.
>
> **Key decision:** Server uses **Haskell via MAlonzo** (Agda's Haskell backend), NOT Node.js.
> Client uses **JS backend** (as now). Same Agda source, two compilation targets.
>
> **Context:** [concurrency.md](concurrency.md) describes browser-side concurrency (Web Workers).
> This document describes the overall dual-backend architecture.

---

## Overview

```
                     Agda source code
                    (shared types, pure logic)
                           /              \
                  agda --js            agda --compile (MAlonzo)
                     ↓                          ↓
              ES modules (.mjs)          Haskell modules (.hs)
                     ↓                          ↓
                Browser                   GHC → native binary
           (runtime/reactive.js)       (hs/Agdelte/Runtime.hs)
```

### Why Haskell for server?

- **MAlonzo** is Agda's most mature backend — better supported than JS backend
- Haskell has **real concurrency**: green threads (millions), STM, async
- `ProcessOptic` maps naturally to Haskell IPC (Unix sockets, pipes)
- `RemoteOptic` maps naturally to `Network.HTTP` / `warp`
- Type safety carries from Agda through Haskell to the running binary
- STM available directly for complex coordination

### Why NOT Node.js for server?

- Node.js has single-threaded event loop — concurrency via Web Workers is limited
- No STM, no green threads
- Agda's JS backend is less mature than MAlonzo
- Server workloads (many connections, heavy computation) benefit from GHC's runtime

---

## Module Organization

### Agda source (platform-agnostic)

All Agda modules in `src/Agdelte/` are **pure types and logic** — they contain no
platform-specific FFI. They compile cleanly to both JS and Haskell backends.

```
src/Agdelte/
  Core/                    -- pure Agda, both backends
    Event.agda             -- Event AST (interval, keyboard, worker, channel...)
    Signal.agda            -- Coinductive streams
    Cmd.agda               -- Command AST (httpGet, spawn, send...)
    Task.agda              -- Monadic task chains

  Reactive/                -- pure Agda types (used by JS runtime for DOM)
    Node.agda              -- Template structure, Binding, ReactiveApp
    Lens.agda              -- Lens, fstLens, sndLens
    Optic.agda             -- Prism, Traversal, Affine, Optic, routeMsg

  Concurrent/              -- NEW, pure Agda types (both backends)
    Agent.agda             -- Agent as polynomial coalgebra
    Channel.agda           -- Typed channels
    Protocol.agda          -- Session types / protocols

  Theory/                  -- Mathematical foundation (both backends)
    Poly.agda
    PolySignal.agda

  Test/                    -- Pure tests (both backends)
    Interpret.agda
    OpticTest.agda
```

**Key principle:** No `{-# COMPILE JS #-}` or `{-# COMPILE GHC #-}` pragmas in these files.
They are pure Agda — the compilation target is chosen by the build command, not the source.

### FFI modules (platform-specific)

FFI bindings live in separate modules, one per backend:

```
src/Agdelte/
  FFI/
    Browser.agda           -- {-# COMPILE JS #-} only
                           -- DOM rendering, Web Workers, fetch, WebSocket
    Server.agda            -- {-# COMPILE GHC #-} only
                           -- IO, STM, Network, Process, file system
    Shared.agda            -- Types used by both (serialization, protocols)
```

**Browser.agda** — JS-only FFI:
```agda
-- DOM rendering
postulate
  domRender : Node Model Msg → ...
{-# COMPILE JS domRender = ... #-}

-- Web Worker
postulate
  spawnWorker : String → Event WorkerMsg
{-# COMPILE JS spawnWorker = function(script) { return new Worker(script); } #-}

-- Fetch API
postulate
  fetch : String → Event String
{-# COMPILE JS fetch = ... #-}
```

**Server.agda** — Haskell-only FFI:
```agda
{-# FOREIGN GHC import qualified Control.Concurrent.STM as STM #-}
{-# FOREIGN GHC import qualified Network.Wai as Wai #-}
{-# FOREIGN GHC import qualified Network.Wai.Handler.Warp as Warp #-}
{-# FOREIGN GHC import qualified System.Process as Proc #-}

-- STM
postulate
  TVar      : Set → Set
  newTVar   : A → IO (TVar A)
  readTVar  : TVar A → STM A
  writeTVar : TVar A → A → STM ⊤
  atomically : STM A → IO A

{-# COMPILE GHC TVar = type STM.TVar #-}
{-# COMPILE GHC newTVar = STM.newTVarIO #-}
{-# COMPILE GHC readTVar = STM.readTVar #-}
{-# COMPILE GHC writeTVar = STM.writeTVar #-}
{-# COMPILE GHC atomically = STM.atomically #-}

-- HTTP server
postulate
  listen : ℕ → (Request → IO Response) → IO ⊤
{-# COMPILE GHC listen = \port handler -> Warp.run port (waiHandler handler) #-}

-- Process spawning
postulate
  spawnProcess : String → List String → IO ProcessHandle
{-# COMPILE GHC spawnProcess = \cmd args -> Proc.spawnProcess cmd args #-}
```

### Runtime (platform-specific interpreters)

The runtime interprets Agda's AST types (Event, Cmd, Node) using platform APIs.

```
runtime/                   -- JS runtime (browser) — EXISTS NOW
  reactive.js              -- DOM rendering, binding updates
  reactive-auto.js         -- Auto-loader
  events.js                -- Event interpreter (interval, keyboard, HTTP...)
  core.js                  -- NEW: shared logic (serialization, channel protocol)

hs/                        -- Haskell runtime (server) — NEW
  Agdelte/
    Runtime.hs             -- Agent runner, event loop, channel interpreter
    Transport.hs           -- HTTP server (warp), WebSocket (wai-websockets)
    Process.hs             -- IPC (Unix sockets, pipes), child processes
    STM.hs                 -- STM-based channel implementation
```

---

## Build System

### Current (JS only)

```json
{
  "build:counter": "agda --js --js-es6 --js-optimize --compile-dir=_build ...",
  "build:all": "...",
  "dev": "node serve.cjs"
}
```

### Phase 7 (dual backend)

```json
{
  "build:counter": "agda --js --js-es6 --js-optimize --compile-dir=_build ...",
  "build:all": "...",
  "dev": "node serve.cjs",

  "build:server": "agda --compile --ghc-flag=-O2 -i src server/Main.agda",
  "build:server:dev": "agda --compile -i src server/Main.agda",
  "run:server": "./_build/MAlonzo/server/Main"
}
```

**Agda compilation commands:**
- `agda --js` → JavaScript ES modules (browser)
- `agda --compile` → Haskell via MAlonzo → GHC → native binary (server)

The **same Agda source** compiles to both targets. The difference is:
1. Which FFI module the entry point imports (`Browser.agda` vs `Server.agda`)
2. Which build command is used

### Project structure with server

```
server/                    -- Server entry points (Agda)
  Main.agda                -- Server main: imports FFI.Server, starts agents
  ChatServer.agda          -- Example: chat server agent

examples/                  -- Client entry points (Agda) — as now
  Counter.agda
  Timer.agda
  ...

hs/                        -- Haskell runtime support
  Agdelte/
    Runtime.hs
    Transport.hs
    Process.hs
```

---

## What Is Shared, What Splits

| Layer | Platform | Examples |
|-------|----------|---------|
| **Agda types** | Both | Agent, Channel, Optic, Protocol, Event, Cmd |
| **Pure logic** | Both | update, routeMsg, optic composition, Agent.step |
| **FFI (browser)** | JS only | DOM, Web Worker, fetch, WebSocket (client) |
| **FFI (server)** | Haskell only | IO, STM, Network, Process, file system |
| **Runtime (browser)** | JS only | reactive.js, events.js |
| **Runtime (server)** | Haskell only | Runtime.hs, Transport.hs |
| **Entry point (browser)** | JS only | `runReactiveApp(app)` |
| **Entry point (server)** | Haskell only | `runAgent agent`, `listen port handler` |

### How an Agent type works on both sides

```agda
-- src/Agdelte/Concurrent/Agent.agda (PURE — compiles to both)
record Agent (S I O : Set) : Set where
  field
    state   : S
    observe : S → O
    step    : S → I → S
```

**On client (JS):** The `events.js` runtime interprets Agent by creating a Web Worker
or running step functions in `requestIdleCallback`.

**On server (Haskell):** The `Runtime.hs` interprets Agent by spawning a green thread
(`forkIO`), using `STM.TVar` for state, and `STM.TChan` for input/output.

Same Agda definition → different runtime interpreters → same semantics.

---

## Optic as Uniform Access

The Optic hierarchy from Phase 6 extends naturally to cross-process and cross-host access:

```
Optic (local field access)    — Lens, Prism, Affine (Phase 6, done)
     ↓ same interface
ProcessOptic (IPC)            — peek/over via Unix socket or pipe
     ↓ same interface
RemoteOptic (HTTP)            — peek/over via HTTP GET/PUT
```

All three use the same `Optic S A` interface: `peek : S → Maybe A`, `over : (A → A) → S → S`.

- **Local:** direct function call (as now)
- **Process:** serialize optic operation → IPC → deserialize result
- **Remote:** serialize optic operation → HTTP → deserialize result

The Agda types are the same. The transport differs:

```agda
-- Pure optic (Phase 6, exists)
localOptic : Optic Model Item
localOptic = fromAffine (ixList n) ∘O fromLens itemsLens

-- Process optic (Phase 7, planned)
processOptic : ProcessOptic NetworkState ProcessState
-- Haskell runtime: sends operation via Unix socket

-- Remote optic (Phase 7, planned)
remoteOptic : RemoteOptic ClusterState HostState
-- Haskell runtime: sends operation via HTTP
```

---

## Haskell Runtime Details

### Agent runner

```haskell
-- hs/Agdelte/Runtime.hs
module Agdelte.Runtime where

import Control.Concurrent (forkIO)
import Control.Concurrent.STM

-- Run an Agent as a green thread
runAgent :: Agent s i o -> IO (TChan i, TChan o)
runAgent agent = do
  stateVar <- newTVarIO (agentState agent)
  inChan   <- newTChanIO
  outChan  <- newTChanIO
  forkIO $ loop agent stateVar inChan outChan
  return (inChan, outChan)
  where
    loop agent stateVar inChan outChan = do
      input <- atomically $ readTChan inChan
      newState <- atomically $ do
        s <- readTVar stateVar
        let s' = agentStep agent s input
        writeTVar stateVar s'
        return s'
      let output = agentObserve agent newState
      atomically $ writeTChan outChan output
      loop agent stateVar inChan outChan
```

### HTTP transport (for RemoteOptic)

```haskell
-- hs/Agdelte/Transport.hs
module Agdelte.Transport where

import Network.Wai.Handler.Warp (run)

-- Expose Agent via HTTP
serveAgent :: Int -> Agent s i o -> IO ()
serveAgent port agent = do
  (inChan, outChan) <- runAgent agent
  run port $ \req respond -> do
    -- POST /step  → send input to agent
    -- GET  /state → read current output
    ...
```

### IPC transport (for ProcessOptic)

```haskell
-- hs/Agdelte/Process.hs
module Agdelte.Process where

import System.Process
import Network.Socket

-- Connect to Agent in another process via Unix socket
connectAgent :: FilePath -> IO (TChan i, TChan o)
connectAgent socketPath = do
  sock <- socket AF_UNIX Stream defaultProtocol
  connect sock (SockAddrUnix socketPath)
  -- Wrap socket in TChan interface
  ...
```

---

## GHC Dependencies

Server runtime needs these Haskell packages:

```
-- For a cabal file or stack.yaml
dependencies:
  - base >= 4.14
  - stm >= 2.5              -- STM (TVar, TChan)
  - async >= 2.2            -- Structured concurrency
  - warp >= 3.3             -- HTTP server
  - wai >= 3.2              -- WAI interface
  - wai-websockets >= 3.0   -- WebSocket support
  - aeson >= 2.0            -- JSON serialization
  - network >= 3.1          -- Unix sockets, TCP
  - process >= 1.6          -- Child processes
  - bytestring >= 0.11
  - text >= 2.0
```

---

## Implementation Phases

### Phase 7A: Basic dual-backend (start here)

1. Verify MAlonzo works: compile a simple pure Agda module to Haskell, run it
2. Create `hs/` directory with minimal `Runtime.hs`
3. Create `server/Main.agda` — simplest possible server (echo agent)
4. Create `src/Agdelte/FFI/Server.agda` with basic IO postulates
5. Build script: `agda --compile server/Main.agda`
6. Test: run the binary, send a message, get response

### Phase 7B: Agent + channels

1. Define `Agent` coalgebra in `src/Agdelte/Concurrent/Agent.agda` (pure Agda)
2. Implement `runAgent` in `hs/Agdelte/Runtime.hs` (Haskell, STM-based)
3. Implement `worker` in `runtime/events.js` (JS, Web Worker-based)
4. Same Agent type → runs on both platforms
5. Example: computation agent (server) + UI (browser)

### Phase 7C: ProcessOptic + RemoteOptic

1. Extend Optic to support serialized operations
2. `ProcessOptic`: Haskell runtime interprets via Unix socket
3. `RemoteOptic`: Haskell runtime interprets via HTTP
4. JS client uses `fetch` to talk to Haskell server via RemoteOptic
5. Example: browser UI → HTTP → Haskell server → agent state

### Phase 7D: Wiring diagrams

1. Compose agents via polynomial wiring diagrams
2. Channel topology defined in Agda, interpreted by Haskell runtime
3. Structured concurrency: parent agent cancellation → child cancellation
4. Example: chat system with multiple agents

---

## Client-Server Communication

The browser client and Haskell server communicate via standard HTTP/WebSocket:

```
┌─────────────────────────┐         ┌─────────────────────────┐
│  Browser (JS)           │  HTTP/  │  Server (Haskell/GHC)   │
│                         │   WS    │                         │
│  ReactiveApp            │ ◄─────► │  Agent (green threads)  │
│  Node, Binding          │         │  STM channels           │
│  Event → DOM updates    │         │  ProcessOptic (IPC)     │
│                         │         │  RemoteOptic (HTTP)     │
│  runtime/reactive.js    │         │  hs/Agdelte/Runtime.hs  │
│  runtime/events.js      │         │  hs/Agdelte/Transport.hs│
└─────────────────────────┘         └─────────────────────────┘
         ↑                                    ↑
         │                                    │
    agda --js                          agda --compile
         │                                    │
         └────── Same Agda source ────────────┘
```

### Serialization

Shared types (Agent state, messages, optic operations) need serialization
for cross-process / cross-host communication:

```agda
-- src/Agdelte/FFI/Shared.agda
-- Serialization interface (both backends implement)
record Serialize (A : Set) : Set where
  field
    encode : A → String     -- to JSON
    decode : String → Maybe A  -- from JSON
```

- **JS:** `JSON.stringify` / `JSON.parse`
- **Haskell:** `aeson` `ToJSON` / `FromJSON`

---

## Relation to Existing Documents

| Document | Relation |
|----------|----------|
| [concurrency.md](concurrency.md) | Browser-side concurrency (Web Workers). Still valid for JS runtime. |
| [../doc/api.md](../doc/api.md) | Current API (Node, Event, Cmd, Optic). Phase 7 extends, doesn't replace. |
| [../doc/roadmap.md](../doc/roadmap.md) | Phase 7 entry. This document details the architecture. |
| [../doc/architecture.md](../doc/architecture.md) | Core architecture. Dual-backend is an extension. |
| [../doc/polynomials.md](../doc/polynomials.md) | Agent as coalgebra — the theoretical foundation. |

---

## Summary

**Architecture decision:** Agda compiles to JS (browser) and Haskell (server) from the same source.

**What is shared:** All Agda types, pure logic, optic hierarchy, agent definitions.

**What splits:** FFI bindings (JS DOM vs Haskell IO/STM) and runtime interpreters.

**Why Haskell:** Real concurrency (green threads, STM), mature MAlonzo backend, type safety all the way down.

**The Optic interface is the unifying abstraction:**
- Local: direct field access (Phase 6, done)
- Process: IPC via Unix socket (Phase 7, Haskell runtime)
- Remote: HTTP (Phase 7, Haskell server ↔ JS client)

Same `peek`/`over` interface at every scale.
