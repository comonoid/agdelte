# Research: Unimplemented Design Ideas

> **Status:** Research-level. Nothing below is implemented yet.
>
> All implemented features are documented in [api.md](api.md) and [roadmap.md](roadmap.md).

---

## 1. Wiring Diagrams: Polynomial Composition of Agents

> **Prerequisites:** Agent coalgebra (done), Optic hierarchy (done), ProcessOptic/RemoteOptic (done).
>
> **Theory:** [polynomials.md](polynomials.md)

### Overview

An Agent is a polynomial coalgebra: `Agent S I O` with `state : S`, `observe : S → O`, `step : S → I → S`.

**Wiring diagrams** compose agents by connecting outputs of one to inputs of another,
forming a larger composite agent. This is the polynomial functor composition from
David Spivak's theory.

Currently agents are composed manually (e.g., `MultiAgent.agda` wires counter + toggle
by hand). Wiring diagrams would make this compositional and type-safe.

### Wiring as morphism of polynomials

Each agent defines a polynomial `p(y) = Σ_{i ∈ I} y^{O_i}`:
- Positions = input types
- Directions = output types

A **wiring diagram** is a morphism between polynomials: it maps outputs of inner agents
to inputs of other inner agents (or to the composite's external interface).

```
┌─────────────────────────────────────┐
│            Composite Agent          │
│                                     │
│  ┌─────────┐      ┌─────────┐      │
│  │ Agent A  │─O_A──│ Agent B  │     │
│  │  I_A→O_A │      │  I_B→O_B │─────┼──► External Output
│  └─────────┘      └─────────┘      │
│       ▲                             │
│       │                             │
│  External Input ────────────────────┤
└─────────────────────────────────────┘
```

### Agda representation

```agda
-- A wiring diagram connecting agents into a composite
record Wiring (agents : List AgentSig) (I O : Set) : Set where
  field
    -- Route external input to inner agents
    routeInput : I → HList (map AgentSig.I agents)

    -- Route inner outputs to inner inputs (feedback loops)
    routeFeedback : HList (map AgentSig.O agents)
                  → HList (map AgentSig.I agents)

    -- Combine inner outputs into external output
    routeOutput : HList (map AgentSig.O agents) → O

-- AgentSig: signature (I, O types) without state
record AgentSig : Set₁ where
  field
    I O : Set
```

### Composite agent from wiring

```agda
-- Given concrete agents and a wiring diagram, produce a composite agent
wire : (w : Wiring sigs I O)
     → HList (map (λ sig → Agent sig.S sig.I sig.O) sigs)
     → Agent (HList states) I O
wire w agents = record
  { state   = hmap agentState agents
  ; observe = λ ss → w.routeOutput (hzipWith agentObserve agents ss)
  ; step    = λ ss i →
      let inputs   = w.routeInput i
          outputs  = hzipWith agentObserve agents ss
          feedback = w.routeFeedback outputs
          combined = hzipWith (_⊕_) inputs feedback  -- merge external + feedback
      in hzipWith₃ agentStep agents ss combined
  }
```

### Use Cases

#### Pipeline (A → B → C)

```agda
-- Agent A produces tokens, Agent B processes them, Agent C aggregates
pipeline : Wiring [ tokenizer , processor , aggregator ] String Report
pipeline = record
  { routeInput    = λ s → s ∷ "" ∷ "" ∷ []
  ; routeFeedback = λ (oA ∷ oB ∷ oC ∷ []) → "" ∷ oA ∷ oB ∷ []
  ; routeOutput   = λ (_ ∷ _ ∷ oC ∷ []) → oC
  }
```

#### Feedback loop (A ↔ B)

```agda
-- Two agents that feed each other
feedback : Wiring [ agentA , agentB ] I O
feedback = record
  { routeInput    = λ i → i ∷ "" ∷ []
  ; routeFeedback = λ (oA ∷ oB ∷ []) → oB ∷ oA ∷ []  -- cross-wire
  ; routeOutput   = λ (_ ∷ oB ∷ []) → oB
  }
```

#### Broadcast (one input → many agents)

```agda
broadcast : Wiring [ a1 , a2 , a3 ] I (O₁ × O₂ × O₃)
broadcast = record
  { routeInput    = λ i → i ∷ i ∷ i ∷ []    -- same input to all
  ; routeFeedback = λ _ → "" ∷ "" ∷ "" ∷ []  -- no feedback
  ; routeOutput   = λ (o1 ∷ o2 ∷ o3 ∷ []) → (o1 , o2 , o3)
  }
```

### Distributed Wiring

Wiring diagrams extend naturally to distributed agents via ProcessOptic/RemoteOptic:

```agda
-- Same wiring, but agents live in different processes/hosts
distributedWire : Wiring sigs I O
                → HList (map AgentLocation sigs)  -- local, process, or remote
                → DistributedAgent I O

data AgentLocation : AgentSig → Set where
  local   : Agent S I O → AgentLocation sig
  process : ProcessOptic O → AgentLocation sig    -- Unix socket
  remote  : RemoteOptic O → AgentLocation sig     -- HTTP
```

The wiring diagram is the same regardless of whether agents are local, in another
process, or on another host. Only the transport differs.

### Implementation Plan

1. **Define `AgentSig` and `Wiring` record** in `src/Agdelte/Concurrent/Wiring.agda`
2. **Implement `wire` function** — pure composition, no runtime needed
3. **Add HList utilities** — heterogeneous list operations (`hmap`, `hzipWith`, etc.)
4. **Distributed wiring** — extend `wire` to use ProcessOptic/RemoteOptic for remote agents
5. **Examples** — pipeline, feedback loop, fan-out/fan-in patterns
6. **Runtime support** — interpret wired agents on both JS (Workers) and Haskell (green threads)

### Challenges

- **HList in Agda:** heterogeneous lists require universe polymorphism; may need `--type-in-type` or careful level management
- **Input merging:** when an agent receives both external input and feedback, need a merge strategy (e.g., `_⊕_ : I → I → I`)
- **Distributed step semantics:** when agents are remote, `step` becomes async; wiring must handle latency
- **Cycles:** feedback loops must be well-founded to avoid infinite loops in a single tick

### References

- David Spivak, "Poly: An abundant categorical setting for mode-dependent dynamics"
- David Spivak & Nelson Niu, "Polynomial Functors: A General Theory of Interaction"
- [polynomials.md](polynomials.md) — Agdelte-specific polynomial theory

---

## 2. Linear Types for Resources

> **Context:** Concurrency primitives (workers, pools, channels, SharedArrayBuffer) are implemented.
> Linear types would add static guarantees about resource usage.

### Motivation

Workers, channels, shared buffers, and IPC handles are **resources** that must be:
- Used exactly once (not duplicated)
- Eventually freed (not leaked)

Currently, the declarative TEA model handles this automatically — events disappearing
from `subs` triggers cleanup. But for **explicit low-level control** (e.g., manual
IPC handle management, shared buffer ownership), linear types provide static guarantees.

### Design: Indexed Types (most practical for Agda)

Agda lacks built-in linear types, but indexed types can emulate resource tracking:

```agda
-- Resource lifecycle states
data ResourceState : Set where
  Fresh  : ResourceState   -- just created, not yet used
  Open   : ResourceState   -- actively in use
  Closed : ResourceState   -- freed/released

-- Indexed handle: state tracked in type
data Handle (A : Set) : ResourceState → Set where
  mkHandle : HandleId → Handle A Open

-- Operations transition between states
open : Handle A Fresh → IO (Handle A Open)
use  : Handle A Open  → IO (A × Handle A Open)    -- borrow (still Open)
close : Handle A Open  → IO (Handle A Closed)

-- Cannot use a Closed handle — no constructor matches
-- Cannot close a Fresh handle — type mismatch
-- close (close h) — doesn't typecheck (Closed ≠ Open)
```

### Application to existing types

#### IpcHandle (ProcessOptic)

```agda
data IpcState : Set where Connected Disconnected : IpcState

data IpcHandle : IpcState → Set where
  mkIpc : RawHandle → IpcHandle Connected

queryProcess : IpcHandle Connected → IO (String × IpcHandle Connected)
stepProcess  : IpcHandle Connected → String → IO (String × IpcHandle Connected)
closeProcess : IpcHandle Connected → IO (IpcHandle Disconnected)

-- Guarantees:
-- ✓ Cannot query after disconnect
-- ✓ Cannot disconnect twice
-- ✓ Must eventually disconnect (via obligation tracking)
```

#### SharedBuffer

```agda
data BufferState : Set where Owned Shared Released : BufferState

data SharedBuffer : BufferState → Set where
  mkBuffer : RawBuffer → SharedBuffer Owned

-- Transfer ownership to worker
shareBuffer : SharedBuffer Owned → IO (SharedBuffer Shared)

-- Reclaim after worker is done
reclaimBuffer : SharedBuffer Shared → IO (SharedBuffer Owned)

-- Release buffer
releaseBuffer : SharedBuffer Owned → IO (SharedBuffer Released)

-- Guarantees:
-- ✓ Cannot read/write while shared with worker
-- ✓ Cannot share twice without reclaiming
-- ✓ Must eventually release
```

#### Worker Channel

```agda
data ChanState : Set where Active Closed : ChanState

data TypedChannel (S R : Set) : ChanState → Set where
  mkChan : RawChannel → TypedChannel S R Active

send  : TypedChannel S R Active → S → IO (TypedChannel S R Active)
recv  : TypedChannel S R Active → IO (R × TypedChannel S R Active)
close : TypedChannel S R Active → IO (TypedChannel S R Closed)
```

### Obligation Tracking

Linear types alone don't enforce that resources are *eventually* freed.
For that, we need an obligation monad:

```agda
-- Resource obligation: must be discharged before program ends
data Obligation : List ResourceState → Set → Set where
  pure   : A → Obligation [] A
  bind   : Obligation rs A → (A → Obligation rs' B) → Obligation (rs ++ rs') B
  alloc  : Obligation [ Open ] (Handle A Open)
  free   : Handle A Open → Obligation [] (Handle A Closed)

-- run : Obligation [] A → IO A
-- Only programs with empty obligation list can be executed
```

### Practical Considerations

- The declarative TEA model already prevents most resource leaks automatically
- Linear types add value mainly for:
  - Server-side code with explicit handle management (ProcessOptic)
  - SharedArrayBuffer ownership tracking
  - Complex multi-step IPC protocols
- **Recommendation:** implement as an optional layer on top of existing types, not a replacement

---

## 3. Session Types for Protocols

> **Context:** ProcessOptic and worker channels follow implicit communication protocols.
> Session types would make these protocols explicit and statically verified.

### Motivation

Worker channels and IPC connections follow communication **protocols**:
- ProcessOptic: client sends "peek" or "step:INPUT", server responds
- Worker channels: specific message sequences (init → data → done)

Session types encode these protocols in the type system, ensuring both sides agree
on the communication pattern at compile time.

### Design

```agda
-- Session type: describes a communication protocol
data Session : Set₁ where
  Send  : (A : Set) → Session → Session   -- send value of type A, then continue
  Recv  : (A : Set) → Session → Session   -- receive value of type A, then continue
  End   : Session                          -- protocol finished
  Choose : Session → Session → Session     -- offer choice to peer
  Offer  : Session → Session → Session     -- accept choice from peer

-- Duality: the other side's view of the protocol
dual : Session → Session
dual (Send A s) = Recv A (dual s)
dual (Recv A s) = Send A (dual s)
dual End = End
dual (Choose s₁ s₂) = Offer (dual s₁) (dual s₂)
dual (Offer s₁ s₂) = Choose (dual s₁) (dual s₂)
```

### Example: ProcessOptic Protocol

```agda
-- ProcessOptic protocol from the client's perspective
ProcessProtocol : Session
ProcessProtocol = Choose
  -- Option 1: peek
  (Send PeekRequest (Recv String End))
  -- Option 2: step
  (Send StepRequest (Recv String End))

-- Server sees the dual:
-- dual ProcessProtocol = Offer
--   (Recv PeekRequest (Send String End))
--   (Recv StepRequest (Send String End))
```

### Session-typed channels

```agda
-- Channel indexed by remaining protocol
data SessionChan : Session → Set where
  mkChan : RawChannel → SessionChan s

-- Send: consume Send from protocol, continue with rest
send : SessionChan (Send A s) → A → IO (SessionChan s)

-- Recv: consume Recv from protocol, get value and continue
recv : SessionChan (Recv A s) → IO (A × SessionChan s)

-- End: protocol complete, channel is done
end : SessionChan End → IO ⊤

-- Choose: pick one branch
chooseLeft  : SessionChan (Choose s₁ s₂) → IO (SessionChan s₁)
chooseRight : SessionChan (Choose s₁ s₂) → IO (SessionChan s₂)

-- Offer: peer picks, we handle both
offer : SessionChan (Offer s₁ s₂)
      → (SessionChan s₁ → IO A)
      → (SessionChan s₂ → IO A)
      → IO A
```

### Example: typed ProcessOptic client

```agda
peekTyped : SessionChan ProcessProtocol → IO String
peekTyped ch = do
  ch₁ ← chooseLeft ch          -- choose "peek" branch
  ch₂ ← send ch₁ peekRequest   -- send request
  (result , ch₃) ← recv ch₂    -- receive response
  end ch₃                       -- protocol done
  pure result

stepTyped : SessionChan ProcessProtocol → String → IO String
stepTyped ch input = do
  ch₁ ← chooseRight ch              -- choose "step" branch
  ch₂ ← send ch₁ (mkStep input)    -- send step request
  (result , ch₃) ← recv ch₂         -- receive response
  end ch₃                            -- protocol done
  pure result
```

### Example: worker protocol

```agda
-- Worker protocol: send input, receive progress updates, then result
WorkerProtocol : Session
WorkerProtocol =
  Send Input              -- send work item
    (RecvLoop Progress    -- receive progress updates (0 or more)
      (Recv Result End))  -- receive final result

-- RecvLoop: receive 0 or more messages, then continue
data Session where
  ...
  RecvLoop : (A : Set) → Session → Session   -- repeated receive
```

### Relation to Existing Code

| Current | With Session Types |
|---------|--------------------|
| `queryProcess : IpcHandle → IO String` | `send : SessionChan (Send Req s) → Req → IO (SessionChan s)` |
| `stepProcess : IpcHandle → String → IO String` | Sequence of `send` + `recv` with protocol index |
| `workerChannel` + `channelSend` | `SessionChan WorkerProtocol` |
| Protocol violations → runtime error | Protocol violations → type error |

### Implementation Plan

1. **Define `Session` type** in `src/Agdelte/Concurrent/Protocol.agda` (file exists, currently minimal)
2. **Implement `dual`** — mechanical, straightforward
3. **Define `SessionChan`** — indexed by remaining protocol
4. **Implement operations** (`send`, `recv`, `end`, `choose`, `offer`)
5. **FFI backing** — on Haskell: use existing Unix socket / TCP; on JS: use `postMessage`
6. **Typed wrappers** for ProcessOptic and worker channels
7. **Examples** — typed peek/step client, typed worker protocol

### Challenges

- **RecvLoop / recursive protocols:** session types with loops require coinductive or recursive session types; Agda's guardedness checker may be restrictive
- **Error handling:** what if the connection drops mid-protocol? Need to integrate with `TransportResult`
- **Branching:** `Choose`/`Offer` require runtime tag to select branch; must align Agda type-level choice with wire-level tag
- **Composability with wiring diagrams:** wiring diagrams compose agents; session types describe the wires. These should integrate: a wiring diagram should verify that connected agents have dual session types

---

## References

- David Spivak, "Poly: An abundant categorical setting for mode-dependent dynamics"
- David Spivak & Nelson Niu, "Polynomial Functors: A General Theory of Interaction"
- Philip Wadler, "Propositions as Sessions" (2012)
- Simon Gay & Vasco Vasconcelos, "Linear Type Theory for Asynchronous Session Types" (2010)
- Sam Lindley & J. Garrett Morris, "A Semantics for Propositions as Sessions" (2015)
- Robert Atkey, "Parameterised Notions of Computation" (for indexed monads in Agda)
