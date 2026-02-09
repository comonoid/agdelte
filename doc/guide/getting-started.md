# Getting Started

## Prerequisites

- **Agda** >= 2.6.4 with standard library >= 2.0
- **Node.js** >= 18.0
- **GHC** >= 9.4 (for server examples)

## Project Structure

```
src/Agdelte/           -- Agda library modules
  Reactive/            -- Node, Lens, Optic, BigLens, Diagram, Inspector
  Core/                -- Event, Cmd, Task, Signal
  Concurrent/          -- Agent, Wiring, SharedAgent, Session
  Css/                 -- Typed CSS DSL (Decl, Length, Color, Layout, Animation...)
  Anim/                -- Model-driven animations (Tween, Spring)
  Theory/              -- Poly, formal proofs
  FFI/                 -- Browser, Server, Shared postulates

examples/              -- Browser examples (JS backend)
server/                -- Server examples (GHC backend)
runtime/               -- JavaScript runtime (reactive.js, events.js, primitives.js)
hs/                    -- Haskell support modules (Http, WebSocket, AgentServer)
scripts/               -- Build tools (generate-css.js, generate-anim-data.js)
examples_html/         -- HTML pages for browser examples
  generated/           -- Build artifacts (CSS files, JSON data)
doc/                   -- Documentation
```

## Build & Run (Browser Examples)

```bash
# Build all browser examples (Agda → JS)
npm run build:all

# Start development server
npm run dev

# Open in browser
open http://localhost:8080
```

Individual examples:

```bash
npm run build:counter        # Counter
npm run build:timer          # Timer
npm run build:todo           # Todo list
npm run build:keyboard       # Keyboard events
npm run build:http           # HTTP requests
npm run build:task           # Task chains
npm run build:websocket      # WebSocket
npm run build:router         # SPA routing
npm run build:composition    # Component composition
npm run build:transitions    # CSS transitions
npm run build:combinators    # Event combinators
npm run build:optic-dynamic  # Dynamic optics
npm run build:worker         # Web Worker
npm run build:parallel       # Parallel/Race
npm run build:session-form   # Session form
npm run build:stress-test    # Stress test (binding perf)
npm run build:remote-agent   # Remote agent client
npm run build:css-demo       # CSS stylesheet demo
npm run build:css-full-demo  # CSS full feature demo
npm run build:anim-demo      # Animation verification demo
```

### CSS & Animation Data Generation

After compiling CSS/Anim examples, generate static assets:

```bash
npm run css:demo        # CssDemo.agda -> css-demo.css
npm run css:full-demo   # CssFullDemo.agda -> css-full-demo.css
npm run css:anim-data   # AnimDemo.agda -> anim-demo.json
npm run css:all         # All of the above
```

Pipeline: `agda --js` compiles Agda to JS modules, then Node.js scripts
extract CSS text / computed values from the compiled modules into static files.

## Build & Run (Server Examples)

Server examples compile to native Haskell binaries via MAlonzo:

```bash
# Echo agent server (console)
npm run build:main && npm run run:server

# HTTP agent server (used by Remote Agent browser example)
npm run build:server && npm run run:server

# Multi-agent server (counter + toggle, with WebSocket)
npm run build:multi-agent && npm run run:multi-agent

# SharedAgent demo (pure console output)
npm run build:shared-demo && npm run run:shared-demo

# Inspector/Diagram demo (pure console output)
npm run build:inspector-demo && npm run run:inspector-demo
```

## Writing a New Example

### Browser example

1. Create `examples/MyExample.agda`:

```agda
module MyExample where

open import Agdelte.Reactive.Node
open import Agdelte.Core.Event    -- for subscriptions
open import Agdelte.Core.Cmd      -- for commands (ε = no-op)

-- Define Model, Msg, updateModel, template

-- Simple app (no side effects):
app = simpleApp initialModel updateModel myTemplate

-- Or full TEA with commands and subscriptions:
app = mkReactiveApp initialModel updateModel myTemplate cmd' subs'
  where
    cmd' : Msg → Model → Cmd Msg
    cmd' _ _ = ε  -- no commands

    subs' : Model → Event Msg
    subs' _ = never  -- no subscriptions
```

2. Add build script to `package.json`:

```json
"build:my-example": "agda --js --js-es6 --js-optimize --compile-dir=_build -i src -i examples examples/MyExample.agda"
```

3. Create `examples_html/my-example.html` (copy from `counter.html`, change `data-agdelte="MyExample"`).

### Server example

1. Create `server/MyServer.agda` with `main : IO ⊤`.
2. Add GHC build script (copy from `build:server` pattern).
3. Run: `_build/MyServer`.

## Tests

```bash
npm test                    # Runtime tests (JS)
npm run typecheck           # Type-check core modules
npm run typecheck:theory    # Type-check theory modules
```
