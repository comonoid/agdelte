# Agdelte Examples

> See [doc/guide/examples.md](../doc/guide/examples.md) for detailed guide.

Examples demonstrate Agdelte features:

| Example | Description | Features |
|---------|-------------|----------|
| Counter | Counter | Reactive bindings (no VDOM) |
| Timer | Stopwatch | Event subs (interval) |
| Todo | Task list | Lists, filtering, input handling |
| Keyboard | Arrow key control | onKeyDown, global keyboard events |
| Http | HTTP requests | Cmd (httpGet) |
| Task | HTTP chain | Task with do-notation |
| WebSocket | Echo client | wsConnect, wsSend |
| Router | SPA routing | pushUrl, onUrlChange |
| Transitions | CSS animations | whenT, enter/leave transitions |
| Composition | Two counters | zoomNode, shared total |
| Combinators | Event pipeline | foldE, mapFilterE |
| OpticDynamic | Dynamic optics | ixList, Traversal, runtime _∘O_ |
| StressTest | Performance benchmark | ops/sec, 13 bindings, interval |
| AgentWiring | Agent wiring | Agent coalgebra, Wiring |
| DepAgentDemo | Dependent agents | DepAgent |
| Parallel | Parallel execution | Parallel event combinators |
| RemoteAgent | Remote agents | RemoteOptic, cross-host |
| SessionDual | Session duality | Session types, dual proof |
| SessionFormDemo | Session forms | SessionForm |
| Worker | Web workers | worker, offload computation |

## Building

### From project root (recommended)

```bash
# Individual examples
npm run build:counter
npm run build:timer
npm run build:todo
npm run build:keyboard
npm run build:http
npm run build:task
npm run build:websocket
npm run build:router
npm run build:composition
npm run build:transitions
npm run build:combinators
npm run build:optic-dynamic
npm run build:stress-test

# All at once
npm run build:all
```

### From examples directory

```bash
# Counter
agda --js --js-es6 --js-optimize --compile-dir=../_build Counter.agda

# Timer
agda --js --js-es6 --js-optimize --compile-dir=../_build Timer.agda

# Todo
agda --js --js-es6 --js-optimize --compile-dir=../_build Todo.agda
```

### Type checking only (no JS)

```bash
agda Counter.agda
agda Timer.agda
agda Todo.agda
```

## Running in browser

1. Start server from project root:
   ```bash
   npm run dev
   ```

2. Open in browser:
   - http://localhost:8080/ — main page
   - http://localhost:8080/examples_html/counter.html — Counter
   - http://localhost:8080/examples_html/timer.html — Timer
   - http://localhost:8080/examples_html/todo.html — Todo
   - http://localhost:8080/examples_html/keyboard.html — Keyboard
   - http://localhost:8080/examples_html/http.html — HTTP
   - http://localhost:8080/examples_html/task.html — Task Chain
   - http://localhost:8080/examples_html/websocket.html — WebSocket
   - http://localhost:8080/examples_html/router.html — Router
   - http://localhost:8080/examples_html/transitions.html — Transitions
   - http://localhost:8080/examples_html/composition.html — Composition
   - http://localhost:8080/examples_html/combinators.html — Combinators
   - http://localhost:8080/examples_html/optic-dynamic.html — Dynamic Optics
   - http://localhost:8080/examples_html/stress-test.html — Stress Test

## Example structure

Every example uses Reactive Bindings (like Svelte):

```agda
-- Model: application state
Model = ℕ  -- or record

-- Msg: messages (events)
data Msg : Set where
  Inc Dec : Msg

-- update: state transition
update : Msg → Model → Model

-- template: declarative template with bindings
template : Node Model Msg
template =
  div [ class "counter" ]
    ( button [ onClick Dec ] [ text "-" ]
    ∷ span [ class "count" ] [ bindF show ]   -- auto-updates!
    ∷ button [ onClick Inc ] [ text "+" ]
    ∷ [] )

-- app: assemble application (simple - no cmd/subs)
app : ReactiveApp Model Msg
app = simpleApp init update template

-- Or with commands and subscriptions (full TEA):
app = mkReactiveApp init update template cmd' subs'
  where
    cmd' : Msg → Model → Cmd Msg
    cmd' _ _ = ε

    subs' : Model → Event Msg
    subs' _ = never
```

**Key difference from Virtual DOM**: `template` is data, not a function. Bindings track which DOM nodes need updating.
