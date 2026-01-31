# Agdelte

**Dependently-typed reactive UI on polynomial functors.  
No Virtual DOM.**

The foundation is maximally general:  
polynomial functors and dependent lenses (Spivak, Niu).

The surface is maximally simple:  
`button [ onClick Inc ] [ text "+" ]`

The connection is proven:  
every practical abstraction is an isomorphism away from the general theory.

## The Design Principle

```
General foundation          Simple surface           Proven bridge
─────────────────          ──────────────           ─────────────
Poly { Pos; Dir }    ───>  Lens { get; set }   <──  Lens ≅ Poly.Lens
Coalg p S            ───>  ReactiveApp M Msg   <──  App ≅ Coalg
Poly.Lens P Q        ───>  AgentLens I O I' O' <──  AgentLens = Poly.Lens (refl)
Σ(o:O) y^{I(o)}     ───>  Agent S I O         <──  Agent ≅ Coalg(Mono O I)
SessionI/SessionO    ───>  send A · recv B     <──  dual(dual s) ≡ s
```

You work with the right column. The left column exists in `Theory/`. The middle column is proved in Agda.

## What It Looks Like

```agda
-- Counter: 8 lines, fully typed, no Virtual DOM
data Msg : Set where Inc Dec : Msg

update : Msg → ℕ → ℕ
update Inc n = suc n
update Dec zero = zero
update Dec (suc n) = n

template : Node ℕ Msg
template =
  div [ class "counter" ]
    ( button [ onClick Dec ] [ text "-" ]
    ∷ span [] [ bindF show ]          -- auto-updates when model changes
    ∷ button [ onClick Inc ] [ text "+" ]
    ∷ [] )

app : ReactiveApp ℕ Msg
app = mkReactiveApp 0 update template
```

Compare to Svelte — same directness, but the type system sees through everything:

```svelte
<script> let count = 0; </script>
<div class="counter">
  <button on:click={() => count--}>-</button>
  <span>{count}</span>
  <button on:click={() => count++}>+</button>
</div>
```

## Why No Virtual DOM

`template` is **data**, not a function. It's a static tree with `bind` points that track which DOM nodes depend on which parts of the model.

```
FIRST RENDER:  walk tree → create real DOM → remember (DOMNode, Binding) pairs
MODEL CHANGE:  for each binding: old value vs new value → update if different
```

O(bindings), not O(tree). Same as Svelte's compiled output, but explicit and verifiable.

## Performance

Despite Agda's unoptimized JavaScript backend, Agdelte holds 60 FPS with **1,000,000 pure state updates per frame** and 19 reactive bindings (`StressTest.agda`). The reason: O(bindings) DOM updates, not O(tree). The framework does almost no work at render time — it checks a handful of binding values and patches only what changed.

The bottleneck is never the framework. It's how fast your `update` function runs.

## Architecture: Three Levels

```
Level 3    DSL           button [ onClick Dec ] [ bindF show ]
                         You write this. Types verify it.
           ─────────────────────────────────────────────────
Level 2    Lenses        Lens { get; set }, Optic, zoomNode
                         Composition, navigation, refactoring.
           ─────────────────────────────────────────────────
Level 1    Polynomials   Poly { Pos; Dir }, Coalg, Poly.Lens
                         Mathematical foundation. Proves everything composes.
```

Each level is usable independently. Level 1 is optional — you never need to touch `Theory/` to build apps. But it's there, and it guarantees that every combinator composes correctly by construction.

## The Isomorphism Layer

Every practical type in Agdelte is a proven special case of the polynomial foundation:

| Practical type | General form | Proof |
|---|---|---|
| `Lens S A` | `Poly.Lens (Mono S S) (Mono A A)` | `OpticPolyLens`: round-trip `refl` |
| `ReactiveApp M Msg` | `Coalg (AppPoly)` | `PolyApp`: structure-preserving |
| `Signal A` | `Coalg (Mono A ⊤)` | `PolySignal`: definitional |
| `Agent S I O` | `Coalg (Mono O I)` | `AgentCoalg`: round-trip `refl` |
| `AgentLens I₁ O₁ I₂ O₂` | `Poly.Lens (Mono O₁ I₁) (Mono O₂ I₂)` | Identity (type alias) |
| `BigLens` | `Coalg (Mono O I)` | `BigLensPolyLens`: composition preserved |
| `dual (dual s)` | `s` | `SessionDualProof`: propositional equality |

The proofs live in `src/Agdelte/Theory/`. They don't affect the runtime — they're compile-time guarantees that the convenient surface types are mathematically equivalent to the general framework.

## Composition

Everything composes because everything is a polynomial lens:

```agda
-- Field access
fstLens : Lens (A × B) A

-- Component embedding
zoomNode : (M → M') → (Msg' → Msg) → Node M' Msg' → Node M Msg
zoomNodeL : Lens M M' → Prism Msg Msg' → Node M' Msg' → Node M Msg

-- Agent wiring (= Poly.Lens composition)
_>>>_ : Agent pipeline        -- sequential (◁)
_***_ : Agent parallel        -- tensor (⊗)
_&_   : Agent external choice -- with (&)
_⊕_   : Agent internal choice -- plus (⊕)

-- Same lens interface across processes and hosts
ProcessOptic : Optic across Unix sockets
RemoteOptic  : Optic across WebSocket
BigLens      : Optic across anything
```

The **Big Lens** principle: `peek`/`over` works the same whether you're reading a record field, querying a local agent, or inspecting a remote server.

## Effects

```agda
-- Events = subscriptions (declarative, diffable)
interval   : ℕ → A → Event A
onKeyDown  : (KeyboardEvent → Maybe A) → Event A
wsConnect  : String → (WsMsg → A) → Event A
worker     : WorkerFn A B → A → Event B     -- Web Workers
merge      : Event A → Event A → Event A
foldE      : A → (B → A → A) → Event B → Event A

-- Commands = one-shot effects
httpGet    : String → (String → A) → (String → A) → Cmd A
focus      : String → Cmd A
pushUrl    : String → Cmd A

-- Tasks = monadic chains
fetchChain : Task String
fetchChain = do
  user  ← http "/api/user"
  posts ← http ("/api/users/" ++ userId user ++ "/posts")
  pure (format posts)
```

Events are AST data — the runtime interprets them, diffs subscriptions, manages cleanup automatically.

## Concurrency

Agents are polynomial coalgebras with a convenient record interface:

```agda
record Agent (S I O : Set) : Set where
  field
    state   : S
    observe : S → O       -- output (position in polynomial)
    step    : S → I → S   -- transition (direction in polynomial)
```

Session types compile to agent interfaces:

```agda
data Session : Set₁ where
  send recv : (A : Set) → Session → Session
  offer choose : Session → Session → Session
  done : Session

-- dual swaps send↔recv, offer↔choose
-- dual (dual s) ≡ s — proved in SessionDualProof
```

Structured concurrency, automatic resource management, linear obligation tracking.

## Quick Start

```bash
# Agda 2.6.4+, agda-stdlib 2.0+
npm run build:all
npm run dev
# http://localhost:8080/
```

## Project Structure

```
src/Agdelte/
  Reactive/       Node, Binding, Lens, Optic, BigLens — the DSL layer
  Core/           Signal, Event, Cmd, Task, Result — effects
  Concurrent/     Agent, Session, Wiring, SharedAgent — concurrency
  Html/           HTML elements, attributes, events — DSL helpers
  Theory/         Poly, Coalg, Lens, isomorphism proofs — foundation
  FFI/            Browser/Server postulates
  Test/           Pure interpretation, optic proofs

examples/         Counter, Timer, Todo, Router, WebSocket, Agents, ...
runtime/          JavaScript: reactive.js, events.js, dom.js
```

## Documentation

| | |
|---|---|
| [Guide](doc/guide/) | [Architecture](doc/guide/architecture.md), [Getting Started](doc/guide/getting-started.md), [Examples](doc/guide/examples.md) |
| [API](doc/api/) | [Node](doc/api/node.md), [Event](doc/api/event.md), [Cmd](doc/api/cmd.md), [Task](doc/api/task.md), [Optic](doc/api/optic.md), [Agent](doc/api/agent.md), [Signal](doc/api/signal.md), [Session](doc/api/session.md), [FFI](doc/api/ffi.md) |
| [Theory](doc/theory/) | [Polynomials](doc/theory/polynomials.md), [Combinators](doc/theory/combinators.md), [Time Model](doc/theory/time-model.md) |
| [Internals](doc/internals/) | [Runtime](doc/internals/runtime.md) |
| [Comparison](doc/comparison/) | [vs Svelte](doc/comparison/vs-svelte.md), [vs Vue 3](doc/comparison/vs-vue3.md) |

## What's Built

- **Reactive core** — Signal, Event (30+ combinators), Cmd, Task with do-notation
- **No-VDOM rendering** — Node, Binding, keyed lists (`foreachKeyed`), CSS transitions (`whenT`)
- **Optics hierarchy** — Lens, Prism, Affine, Traversal, unified `Optic` with `_∘O_`, 16 propositional equality proofs
- **Component composition** — `zoomNode`, `zoomNodeL`, `routeMsg`, automatic message routing
- **Concurrency** — Agent coalgebras, wiring diagrams, session types, shared/linear agents, Web Workers
- **Big Lens** — same `peek`/`over` across local state, Unix sockets, WebSocket, with composition proofs
- **DevTools** — Network inspector via Big Optic (`Inspector.agda`), time-travel debugging (`TimeTravel.agda`), hot reload (API-level: `app.hotReload(newModule)` preserves model; no automatic file-watch — intentionally left to the caller)
- **Formal proofs** — 9 Theory modules: `Lens ≅ Poly.Lens`, `Agent ≅ Coalg`, `dual(dual s) ≡ s`, lens category laws, ...
- **20 examples** — 12 browser (Counter, Todo, Router, Http, WebSocket, ...), 8 server/agent (AgentWiring, Sessions, RemoteAgent, ...)

## What's Next

Richer DevTools UI. More formal properties (full coherence conditions, functoriality).

## License

MIT
