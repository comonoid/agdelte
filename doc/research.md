# Research: Unimplemented Design Ideas

> **Status:** Research-level. Only topics that are NOT yet implemented or only partially explored.
>
> All implemented features are documented in [api.md](api.md) and [roadmap.md](roadmap.md).

---

## 1. Obligation Monad for Resource Tracking

> **Status:** Not implemented. The basic indexed `IpcHandleL` is done (see `ProcessOpticLinear.agda`), but the obligation monad ensuring handles are EVENTUALLY closed is not.
>
> **Prerequisites:** ProcessOpticLinear.agda (done).

### Problem

Indexed types prevent *misuse* (query after close), but don't prevent *forgetting* to close. A program that connects but never closes typechecks fine.

### Design

```agda
data Obligation : List ResourceState → Set → Set where
  pure  : A → Obligation [] A
  bind  : Obligation rs A → (A → Obligation rs' B) → Obligation (rs ++ rs') B
  alloc : Obligation [ Open ] (Handle A Open)
  free  : Handle A Open → Obligation [] (Handle A Closed)

-- run : Obligation [] A → IO A
-- Only empty-obligation programs can execute
```

### Extension: SharedBuffer ownership

```agda
data BufState : Set where Owned Shared Released : BufState

data SharedBuffer : BufState → Set where
  mkBuf : RawBuffer → SharedBuffer Owned

share   : SharedBuffer Owned → IO (SharedBuffer Shared)
release : SharedBuffer Owned → IO (SharedBuffer Released)
-- Cannot release a Shared buffer; cannot write to Released
```

### Integration with session types

Session protocol completion could guarantee handle cleanup: if you reach `done`, the handle must be closed.

---

## 2. Dependent Polynomials (DepAgent)

> **Status:** Theoretical design. May never be needed if current fixed-fiber approach suffices.
>
> **Prerequisites:** Agent (done), Wiring (done).

### Motivation

Current `Agent S I O` has fixed fibers: input type `I` doesn't depend on observation `O`.
The full polynomial `p(y) = Σ(o:O) y^{I(o)}` allows input to depend on current observation.

This matters for **⊕ (internal choice)**: when state is `inj₁ s₁`, input should be `I₁` not `I₁ ⊎ I₂`.

### Design

```agda
record DepAgent (S : Set) (O : Set) (I : O → Set) : Set where
  field
    state   : S
    observe : S → O
    step    : (s : S) → I (observe s) → S
```

### When needed

- **Full ⊕ correctness:** currently `_⊕_` accepts `I₁ ⊎ I₂` with no-op on mismatch. DepAgent would make mismatched input a type error.
- **Dependent protocols:** a server whose available commands depend on its current state (e.g., can't `withdraw` when balance = 0).
- **Formal proofs:** `Agent ↔ Coalg P` correspondence is exact only with DepAgent.

### When NOT needed

- **Wiring is correct:** the AgentLens `bwd : O → I' → I` already routes inputs correctly based on observation. If you compose using Wiring combinators, tags always match.
- **Practical code:** in all existing examples, fixed-fiber agents work fine.
- **Error messages:** DepAgent introduces `I (observe s)` in types, making errors dependent-type-flavored.

### Recommendation

**Don't implement unless a concrete example demands it.** The current `Agent S I O` + `AgentLens` covers all known use cases. DepAgent is a theoretical escape hatch documented here for completeness.

### If implementing

1. Define `DepAgent` in `src/Agdelte/Concurrent/DepAgent.agda`
2. `Agent S I O ≅ DepAgent S O (const I)` — embedding
3. Redefine `_⊕_` for DepAgent with exact fiber
4. Provide `forget : DepAgent S O I → Agent S (Σ O I) O` — flatten to fixed-fiber

---

## 3. ! (Bang) — Shareable Agents

> **Status:** Partially implemented (ProcessOptic / RemoteOptic serve as !), not formalized.

### Concept

In linear logic, `!A` means "unlimited copies of A". For agents: an agent that can serve multiple clients simultaneously.

### What exists

- `ProcessOptic` — multiple processes connect to one agent via Unix socket
- `RemoteOptic` — multiple browsers connect to one agent via HTTP
- `AgentServer.hs` — one agent, many WS subscribers

All of these are implicitly `!Agent` — one state, many readers/writers.

### What's missing

Formal type-level distinction between:
- **Linear agent:** consumed by one interaction (e.g., one-shot worker)
- **Shareable agent:** serves many (e.g., persistent server agent)

```agda
record SharedAgent (I O : Set) : Set₁ where
  field
    {S}   : Set
    agent : Agent S I O
```

### Recommendation

Low priority. The existing ProcessOptic/RemoteOptic pattern works. Formalize only when building the proof framework (Phase 10).

---

## 4. Recursive / Coinductive Sessions

> **Status:** Not explored.
>
> **Prerequisites:** Session.agda (done).

### Problem

Current `Session` is a finite inductive type — protocols must terminate. Real protocols often loop (e.g., "receive messages until disconnect").

### Options

1. **`μ` binder:** add `rec : (Session → Session) → Session` — self-referencing session. Requires guardedness.
2. **Coinductive Session:** use Agda's `record` with `--guardedness` for infinite protocols.
3. **External loop:** keep Session finite, wrap in IO loop at the runtime level.

### Challenges

- Agda's guardedness checker may reject useful recursive session patterns.
- `SessionI`/`SessionO` would need to be coinductively defined too.
- Option 3 is simplest but loses type-level protocol guarantees for the loop.

---

## 5. Multi-step Session Execution

> **Status:** Partially designed in Session.agda comments, not implemented.
>
> **Prerequisites:** Session.agda (done), Wiring.agda `_>>>_` (done).

### Problem

An `Agent S I O` has ONE step function: `step : S → I → S`. But a session like `Send A (Recv B End)` has TWO steps.

### Solution sketch

Encode session state in the Agent state type using an indexed state machine, or compile the entire multi-step session into a SINGLE Agent whose state tracks progress. `_>>>_` from Wiring.agda composes individual steps.

```agda
-- Each step is an Agent, pipeline composes them:
-- stepAgent1 >>> stepAgent2 >>> stepAgent3
-- State = (S₁ × S₂ × S₃), tracks "which step we're on"
```

This is essentially a coroutine: yield/await encoded as Agent step.

---

## Summary: What to Implement Next

Priority order:

1. **Recursive sessions (§4)** — extends existing Session.agda with looping protocols.
2. **Multi-step execution (§5)** — makes sessions actually runnable as Agent pipelines.
3. **Obligation monad (§1)** — strong "must close" guarantees for handles.
4. **! formalization (§3)** — low, wait for proof phase.
5. **DepAgent (§2)** — only if a concrete example requires it.

---

## References

- David Spivak, "Poly: An abundant categorical setting for mode-dependent dynamics"
- David Spivak & Nelson Niu, "Polynomial Functors: A General Theory of Interaction"
- Philip Wadler, "Propositions as Sessions" (2012)
- Simon Gay & Vasco Vasconcelos, "Linear Type Theory for Asynchronous Session Types" (2010)
- Sam Lindley & J. Garrett Morris, "A Semantics for Propositions as Sessions" (2015)
- Robert Atkey, "Parameterised Notions of Computation" (for indexed monads in Agda)
