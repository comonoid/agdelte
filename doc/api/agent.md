# Agent — Polynomial Coalgebra

From `Agdelte.Concurrent.Agent`.

## Core Type

```agda
record Agent (S I O : Set) : Set where
  field
    state   : S
    observe : S → O
    step    : S → I → S
```

| Function | Type | Description |
|----------|------|-------------|
| `mkAgent` | `S → (S → O) → (S → I → S) → Agent S I O` | Create agent |
| `stepAgent` | `Agent S I O → I → Agent S I O × O` | Step and observe |
| `mapObserve` | `(O → O') → Agent S I O → Agent S I O'` | Map output |
| `mapInput` | `(I' → I) → Agent S I O → Agent S I' O` | Contravariant input map |

---

## Wiring — Agent Composition

From `Agdelte.Concurrent.Wiring`.

### AgentLens

Type alias for `Poly.Lens` on monomial polynomials:

```agda
AgentLens : (I₁ O₁ I₂ O₂ : Set) → Set
AgentLens I₁ O₁ I₂ O₂ = Lens (Mono O₁ I₁) (Mono O₂ I₂)

mkAgentLens : (O₁ → O₂) → (O₁ → I₂ → I₁) → AgentLens I₁ O₁ I₂ O₂
fwd : AgentLens I₁ O₁ I₂ O₂ → O₁ → O₂        -- = onPos
bwd : AgentLens I₁ O₁ I₂ O₂ → O₁ → I₂ → I₁   -- = onDir

through : AgentLens I O I' O' → Agent S I O → Agent S I' O'
```

| Function | Type | Description |
|----------|------|-------------|
| `idAL` | `AgentLens I O I O` | Identity lens (= `idLens`) |
| `_∘AL_` | `AgentLens I₂ O₂ I' O' → AgentLens I₁ O₁ I₂ O₂ → AgentLens I₁ O₁ I' O'` | Compose (= `_∘L_`) |
| `through` | `AgentLens I O I' O' → Agent S I O → Agent S I' O'` | Apply lens to agent |

### Combinators

| Function | Type | Linear Logic | Description |
|----------|------|-------------|-------------|
| `_>>>_` | `Agent S₁ I M → Agent S₂ M O → Agent (S₁ × S₂) I O` | ◁ | Pipeline |
| `_***_` | `Agent S₁ I₁ O₁ → Agent S₂ I₂ O₂ → Agent (S₁ × S₂) (I₁ × I₂) (O₁ × O₂)` | ⊗ | Parallel |
| `_&_` | `Agent S₁ I₁ O₁ → Agent S₂ I₂ O₂ → Agent (S₁ × S₂) (I₁ ⊎ I₂) (O₁ × O₂)` | & | External choice |
| `_⊕_` | `Agent S₁ I₁ O₁ → Agent S₂ I₂ O₂ → Agent (S₁ ⊎ S₂) (I₁ ⊎ I₂) (O₁ ⊎ O₂)` | ⊕ | Internal choice |
| `fanout` | `Agent S₁ I O₁ → Agent S₂ I O₂ → Agent (S₁ × S₂) I (O₁ × O₂)` | Δ | Fan-out |
| `loop` | `Agent S (I × O) O → Agent S I O` | trace | Feedback |
| `selectLeft` | `AgentLens (I₁ ⊎ I₂) (O₁ × O₂) I₁ O₁` | π₁ | Select left branch |
| `selectRight` | `AgentLens (I₁ ⊎ I₂) (O₁ × O₂) I₂ O₂` | π₂ | Select right branch |

### Utilities

| Function | Type | Description |
|----------|------|-------------|
| `mapI` | `(I' → I) → Agent S I O → Agent S I' O` | Contravariant input map |
| `mapO` | `(O → O') → Agent S I O → Agent S I O'` | Covariant output map |
| `remap` | `(I' → I) → (O → O') → Agent S I O → Agent S I' O'` | Both at once |
| `swap` | `Agent S (I₁ × I₂) O → Agent S (I₂ × I₁) O` | Swap inputs |
| `constAgent` | `O → Agent O I O` | Constant output |
| `terminal` | `Agent ⊤ I ⊤` | Unit agent |

### Existential Wrapper

```agda
record SomeAgent (I O : Set) : Set₁ where
  field
    {State} : Set
    agent : Agent State I O

pack : Agent S I O → SomeAgent I O
_>>>ₛ_ _***ₛ_ _&ₛ_ _⊕ₛ_ -- compositions on packed agents
```

---

## SharedAgent — Multiplicity Markers

From `Agdelte.Concurrent.SharedAgent`.

```agda
record SharedAgent (I O : Set) : Set₁ where
  constructor mkShared
  field {S} : Set ; agent : Agent S I O

record LinearAgent (I O : Set) : Set₁ where
  constructor mkLinear
  field {S} : Set ; agent : Agent S I O
```

| Function | Type | Description |
|----------|------|-------------|
| `share` | `Agent S I O → SharedAgent I O` | Mark shareable |
| `asLinear` | `Agent S I O → LinearAgent I O` | Mark one-shot |
| `peekShared` | `SharedAgent I O → O` | Observe (non-destructive) |
| `stepShared` | `SharedAgent I O → I → SharedAgent I O × O` | Step (mutates) |
| `useLinear` | `LinearAgent I O → I → O` | Consume once |
| `_>>>shared_` | `SharedAgent I M → SharedAgent M O → SharedAgent I O` | Pipeline |
| `_***shared_` | `SharedAgent I₁ O₁ → SharedAgent I₂ O₂ → SharedAgent (I₁ × I₂) (O₁ × O₂)` | Parallel |
| `fanoutShared` | `SharedAgent I O₁ → SharedAgent I O₂ → SharedAgent I (O₁ × O₂)` | Fan-out |

### Registry

```agda
record NamedAgent : Set₁ where
  constructor mkNamed
  field agentName agentPath : String ; {I O} : Set ; shared : SharedAgent I O

Registry = List NamedAgent
lookupAgent : String → Registry → Maybe NamedAgent
```

---

## Diagram — Wiring Topology

From `Agdelte.Reactive.Diagram`.

```agda
data Connection : Set where
  broadcast   : String → Connection            -- output → all WS clients
  agentPipe   : String → String → Connection   -- source → target agent
  clientRoute : String → Connection            -- WS input → agent

record Slot : Set₁ where
  field name path : String ; {S} : Set ; agent : Agent S String String

record Diagram : Set₁ where
  field slots : List Slot ; connections : List Connection ; port : Nat
```

### Smart Constructors

```agda
singleAgent : ... → Diagram   -- 1 agent, broadcast + clientRoute
dualAgent   : ... → Diagram   -- 2 agents, both broadcast
pipeline    : ... → Diagram   -- agent1 output → agent2 input
_⊕D_        : Diagram → Diagram → Nat → Diagram  -- merge
wire        : Connection → Diagram → Diagram       -- add connection
```

### IO Bridge

```agda
wireSlot    : Slot → IO AgentDef       -- pure Agent → mutable server
runDiagram1 : Diagram → IO ⊤           -- run 1-agent diagram
runDiagram2 : Diagram → IO ⊤           -- run 2-agent diagram
```

---

## Inspector

From `Agdelte.Reactive.Inspector`.

| Function | Type | Description |
|----------|------|-------------|
| `inspectOne` | `String → IOOptic → IO ⊤` | Peek one optic with label |
| `inspectAll` | `List (String × IOOptic) → IO ⊤` | Inspect list of optics |
| `inspectDiagram` | `Diagram → IO ⊤` | Print all agent states |
| `inspectRemote` | `String → String → IO ⊤` | Inspect via Unix socket |
| `sendCommand` | `IOOptic → String → IO String` | Send input via optic |
| `sendAndPrint` | `String → IOOptic → String → IO ⊤` | Send and print result |
