# Dual-Backend Architecture: JS (Browser) + Haskell (Server)

> **Status:** ✅ Implemented (Phase 7). All sub-phases 7A–7D done.
>
> **Key decision:** Server uses **Haskell via MAlonzo** (Agda's Haskell backend), NOT Node.js.
> Client uses **JS backend** (as now). Same Agda source, two compilation targets.
>
> **Context:** [concurrency.md](concurrency.md) describes browser-side concurrency (Web Workers).
> This document describes the overall dual-backend architecture.
>
> **What was implemented:**
> - **Phase 7A:** Agent coalgebra (`src/Agdelte/Concurrent/Agent.agda`) — compiles to both JS and Haskell
> - **Phase 7B:** Web Worker runtime (`examples/Worker.agda`, `runtime/events.js` worker interpreter)
> - **Phase 7C:** Haskell HTTP server (`server/HttpAgent.agda`, `hs/Agdelte/Http.hs`, `src/Agdelte/FFI/Server.agda`)
> - **Phase 7D:** Browser ↔ Server communication (`examples/RemoteAgent.agda` using `agentQuery`/`agentStep!` Cmd combinators)
> - **Phase 7+:** WebSocket broadcast (`hs/Agdelte/WebSocket.hs`), Multi-Agent routing (`server/MultiAgent.agda`, `hs/Agdelte/AgentServer.hs`), Live Dashboard (`examples_html/live-agent.html`)
>
> **Key files:**
> | File | Role |
> |------|------|
> | `src/Agdelte/Concurrent/Agent.agda` | Pure Agent coalgebra (both backends) |
> | `src/Agdelte/FFI/Server.agda` | Haskell FFI: IO, IORef, HTTP, AgentDef |
> | `src/Agdelte/Core/Cmd.agda` | Cmd with `agentQuery`/`agentStep!` combinators |
> | `server/HttpAgent.agda` | Single-agent HTTP server |
> | `server/MultiAgent.agda` | Multi-agent HTTP+WS server (counter + toggle) |
> | `examples/RemoteAgent.agda` | Browser client talking to Agent server via Cmd |
> | `examples/Worker.agda` | Browser-side Web Worker example |
> | `hs/Agdelte/Http.hs` | Raw-socket HTTP server (no warp dependency) |
> | `hs/Agdelte/WebSocket.hs` | Manual WS framing (no websockets library, uses crypton) |
> | `hs/Agdelte/AgentServer.hs` | Multi-agent server with STM broadcast |
> | `examples_html/live-agent.html` | Live dashboard: WS + HTTP real-time UI |
> | `examples_html/remote-agent.html` | RemoteAgent browser UI |

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

Server runtime uses minimal dependencies — **no warp, no wai, no aeson, no websockets library**.
HTTP and WebSocket are implemented from raw sockets to avoid C library dependencies (e.g. `libz`).

```
-- Actual dependencies (as of Phase 7 implementation)
-- All available via GHC's built-in package environment
dependencies:
  - base >= 4.14
  - network >= 3.1          -- Raw TCP sockets
  - text >= 2.0             -- Text type
  - bytestring >= 0.11      -- ByteString for wire protocol
  - stm >= 2.5              -- STM (TChan for WS broadcast)
  - crypton                  -- SHA1 for WebSocket handshake
  - base64-bytestring       -- Base64 for WebSocket handshake
  - memory                   -- ByteArray (used by crypton)
  - containers               -- Data.Map for agent routing

-- NOT needed (implemented manually):
-- warp, wai                -- Http.hs does raw socket HTTP
-- websockets               -- WebSocket.hs does manual framing
-- aeson                    -- Agent state is Text, no JSON needed
```

Build command (all flags required by GHC):
```bash
agda --compile --compile-dir=_build --ghc-flag=-ihs \
  --ghc-flag="-package network" \
  --ghc-flag="-package text" \
  --ghc-flag="-package bytestring" \
  --ghc-flag="-package crypton" \
  --ghc-flag="-package base64-bytestring" \
  --ghc-flag="-package stm" \
  --ghc-flag="-package memory" \
  --ghc-flag="-package containers" \
  server/MultiAgent.agda
```

---

## Implementation Phases

### Phase 7A: Basic dual-backend ✅

1. ✅ Verified MAlonzo: compiled pure Agda Agent coalgebra to Haskell
2. ✅ Created `hs/Agdelte/Http.hs` — raw-socket HTTP server (no warp, no external deps except network)
3. ✅ Created `server/HttpAgent.agda` — single counter agent exposed via HTTP GET/POST
4. ✅ Created `src/Agdelte/FFI/Server.agda` — IO, IORef, HTTP, `_>>=_`, `pure`, `putStrLn`
5. ✅ Build: `agda --compile --ghc-flag=-ihs --ghc-flag="-package network" --ghc-flag="-package text" --ghc-flag="-package bytestring" server/HttpAgent.agda`
6. ✅ Tested: `curl http://localhost:3000/state` → `"0"`, `curl -X POST /step` → `"1"`

**Key lesson:** All `{-# FOREIGN GHC import ... #-}` must be consolidated at the top of Server.agda — MAlonzo emits them inline, and Haskell requires all imports before definitions.

### Phase 7B: Agent + Web Workers ✅

1. ✅ `Agent S I O` coalgebra in `src/Agdelte/Concurrent/Agent.agda` — pure Agda, compiles to both
2. ✅ `worker` Event primitive in `runtime/events.js` — runs Agda-compiled JS in Web Worker
3. ✅ `examples/Worker.agda` — browser-side worker demo
4. ✅ Same Agent definition runs on server (Haskell green thread + IORef) and browser (Worker)

### Phase 7C: HTTP server + RemoteAgent ✅

1. ✅ Haskell HTTP server with path-based routing (`with`-patterns in Agda, not `if_then_else_`)
2. ✅ `examples/RemoteAgent.agda` — browser client using `Cmd` to talk to server
3. ✅ `agentQuery`/`agentStep!` combinators in `Cmd.agda` — semantic wrappers for Agent interaction
4. ✅ Browser UI (`examples_html/remote-agent.html`) talks to Haskell Agent via fetch

### Phase 7D: Multi-Agent + WebSocket ✅

1. ✅ `hs/Agdelte/WebSocket.hs` — manual WS framing (SHA1 via crypton, base64-bytestring, no websockets lib — avoids missing libz)
2. ✅ `hs/Agdelte/AgentServer.hs` — multi-agent server: path-based HTTP routing + STM `TChan` broadcast to all WS clients
3. ✅ `server/MultiAgent.agda` — counter + toggle agents, `wireAgent` bridges pure Agent to Haskell runtime
4. ✅ `examples_html/live-agent.html` — real-time dashboard: WS subscription + HTTP step buttons
5. ✅ Broadcast format: `"agentName:value"` on each step

### Not yet implemented (deferred)

- `ProcessOptic` — Optic operations via Unix sockets (IPC between OS processes)
- `RemoteOptic` — Optic operations via HTTP (cross-host)
- Wiring diagrams — polynomial composition of agents
- Structured concurrency — parent cancellation cascading to children
- Serialization interface (`Serialize` record for cross-process data)

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
