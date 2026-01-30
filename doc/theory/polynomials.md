# Polynomial Functors in Agdelte

## What Are Polynomial Functors?

A **polynomial functor** is a mathematical object that captures the notion of an *interface*: something that produces outputs and accepts inputs depending on the output.

```agda
record Poly : Set₁ where
  field
    Pos : Set           -- positions (outputs / observations)
    Dir : Pos → Set     -- directions (inputs, dependent on position)
```

The polynomial `p(y) = Σ(i : Pos) y^(Dir i)` generalizes many familiar concepts:

| Polynomial | Pos | Dir | Meaning |
|------------|-----|-----|---------|
| `y^I` | `⊤` | `const I` | Reader / input channel |
| `O × y^I` | `O` | `const I` | State machine (output O, input I) |
| `O × y^⊤` | `O` | `const ⊤` | Stream (output only) |
| `Σ(o:O) y^(I o)` | `O` | `I` | Dependent interface |

A **lens** (morphism between polynomials) maps one interface to another:

```agda
record Lens (P Q : Poly) : Set where
  field
    onPos : Pos P → Pos Q                      -- forward (outputs)
    onDir : ∀ p → Dir Q (onPos p) → Dir P p    -- backward (inputs)
```

---

## Why Polynomials Matter for Agdelte

Polynomial functors provide a **single unifying framework** for everything in Agdelte:

```
                      Poly (interface)
                          │
                          ▼
                  Lens P Q (morphism)
                          │
            ┌─────────────┼─────────────┐
            ▼             ▼             ▼
      Protocol Lens   Widget Lens   Agent Lens
      (WebSocket)     (Model→DOM)   (composition)
```

### One Mechanism for Everything

- **State machines** — Agent as polynomial coalgebra
- **Communication protocols** — Session types as polynomial lenses
- **UI rendering** — Widget Lenses (no Virtual DOM)
- **Compositional systems** — wiring diagrams via polynomial operations

Without polynomials, these would be separate ad-hoc mechanisms. With polynomials, they are all instances of the same structure, composable by construction.

---

## Agent as Polynomial Coalgebra

The core type `Agent S I O` is a **coalgebra** of the polynomial `O × y^I`:

```agda
record Agent (S I O : Set) : Set where
  field
    state   : S
    observe : S → O        -- position: what we output
    step    : S → I → S    -- direction: how inputs transition state

-- This is exactly: S → Σ(o : O) (I → S)
-- i.e., a coalgebra of p(y) = O × y^I
```

This identification gives us:

| Agent operation | Polynomial interpretation |
|----------------|--------------------------|
| `observe` | Map to position |
| `step` | Coalgebra structure map |
| `_>>>_` (pipeline) | Composition of coalgebras (◁) |
| `_***_` (parallel) | Tensor product (⊗) |
| `_&_` (external choice) | Additive conjunction (&) |
| `_⊕_` (internal choice) | Additive disjunction (⊕) |
| `AgentLens` | Morphism in Poly category |

### Dependent Agents

When the input type depends on the output, we get `DepAgent` — the full polynomial coalgebra:

```agda
record DepAgent (S : Set) (O : Set) (I : O → Set) : Set where
  field
    state   : S
    observe : S → O
    step    : (s : S) → I (observe s) → S

-- Coalgebra of p(y) = Σ(o : O) y^{I(o)}
```

This models agents whose accepted inputs depend on their current state — e.g., a protocol that only accepts certain messages in certain states.

---

## Session Types as Polynomial Lenses

Session types describe communication protocols:

```agda
data Session : Set₁ where
  send   : (A : Set) → Session → Session
  recv   : (A : Set) → Session → Session
  offer  : Session → Session → Session
  choose : Session → Session → Session
  done   : Session
```

Each session compiles to a polynomial via `SessionI` (input fiber) and `SessionO` (output position). **Duality** (`send ↔ recv`, `offer ↔ choose`) corresponds to swapping the polynomial's forward and backward maps.

The connection is precise:
- A `SessionAgent s S` is an `Agent S (SessionI s) (SessionO s)` — a coalgebra whose interface polynomial is determined by the protocol.
- `AgentLens` between session agents gives protocol adapters.

### Coinductive Sessions

For infinite/looping protocols, `CoSession` uses Agda's coinductive records:

```agda
record CoSession : Set₁ where
  coinductive
  field
    head  : SessionStep
    left  : CoSession
    right : CoSession
```

This allows expressing protocols like "echo server: recv then send, forever" — which finite `Session` cannot represent.

---

## ReactiveApp as Polynomial Machine

The `ReactiveApp` pattern is a special case:

```
App Model Msg ≅ Coalg(y^Msg)

-- update : Msg → Model → Model
-- This is a coalgebra of the polynomial y^Msg
```

The `_∥_` composition of apps corresponds to the **product of polynomials**:
```
(P × Q)(y) = P(y) × Q(y)
App₁ ∥ App₂ : App (M₁ × M₂) (Msg₁ ⊎ Msg₂)
```

---

## Lenses at Every Scale

The polynomial lens abstraction operates uniformly at all scales:

```agda
-- Field access
fieldLens   : Lens Record Field

-- Component adapter
widgetLens  : Lens ChildPoly ParentPoly

-- Network-wide navigation
networkLens : Lens (Network Widget) (Network Widget')
```

In practice, Agdelte implements this hierarchy:

| Abstraction | Module | What it does |
|-------------|--------|-------------|
| `Lens S A` | `Reactive.Lens` | Navigate/modify record fields |
| `Optic S A` | `Reactive.Optic` | Unified get/set (Lens + Prism + Traversal + Affine) |
| `AgentLens I₁ O₁ I₂ O₂` | `Concurrent.Wiring` | Interface adaptation between agents |
| `IOOptic` | `Reactive.BigLens` | Effectful optic over network transport |

The **Big Lens** principle: the same `peek`/`over` interface works for a local record field, a server-side agent over Unix socket, or a browser client over WebSocket.

---

## Widget Lenses: The Original Vision

The name **Agdelte = Agda + Svelte** reflects the core goal: achieve Svelte's direct DOM updates through polynomial lenses rather than compiler magic.

```agda
-- Model as polynomial
ModelPoly : Set → Poly
ModelPoly M = record { Pos = M ; Dir = λ _ → ⊤ }

-- DOM as polynomial
DOMPoly : Poly
DOMPoly = record { Pos = DOMTree ; Dir = λ _ → Mutation }

-- Widget = Incremental Lens from Model to DOM
Widget : Set → Set
Widget M = IncLens (ModelPoly M) DOMPoly
```

The key insight: the "correct structure" that Svelte extracts from templates at compile time can be expressed as **polynomial lenses** in Agda. The `onDelta` field of `IncLens` propagates model changes directly to DOM mutations — no diffing needed.

Current implementation uses explicit `Binding` records that achieve the same O(bindings) performance as Svelte's compiled output, while being verifiable by Agda's type checker.

---

## Wiring Diagrams

Agent networks are described declaratively as polynomial compositions:

```agda
record Diagram : Set₁ where
  field
    slots       : List Slot        -- named agents
    connections : List Connection   -- wiring rules
    port        : Nat              -- HTTP port
```

Each combinator corresponds to a polynomial operation:

| Combinator | Linear Logic | Polynomial operation |
|------------|-------------|---------------------|
| `_>>>_` | ◁ (composition) | Sequential pipeline |
| `_***_` | ⊗ (tensor) | Parallel, separate I/O |
| `_&_` | & (with) | External choice |
| `_⊕_` | ⊕ (plus) | Internal choice |
| `fanout` | Δ (diagonal) | Same input, both outputs |
| `loop` | trace | Feedback |

---

## Multiplicity: Shared vs Linear Agents

The `!` (bang) modality from linear logic distinguishes:

- **SharedAgent** — serves multiple clients simultaneously (persistent server)
- **LinearAgent** — consumed after single use (one-shot worker)

```agda
share    : Agent S I O → SharedAgent I O
asLinear : Agent S I O → LinearAgent I O
```

This formalizes a pattern already present in the runtime: `AgentServer.hs` serves one agent to many WebSocket clients (shared), while `ProcessOpticLinear` tracks connection state to prevent use-after-close (linear).

---

## Summary: What Polynomials Give the Project

| Without polynomials | With polynomials |
|---------------------|-----------------|
| Ad-hoc agent combinators | Principled composition from Poly category |
| Session types as separate mechanism | Sessions = polynomial lenses |
| Widget rendering unrelated to agents | Both are coalgebras of polynomials |
| No formal connection between layers | Lens hierarchy: field → component → network |
| Hope that things compose correctly | Composition correct by construction |

The polynomial foundation doesn't add complexity for the user — `Agent`, `Lens`, `Session` are all simple records. But it guarantees that the architecture scales: any new feature that fits the polynomial framework automatically composes with everything else.

---

## Formal Proofs (Theory/)

All correspondences are formally verified in `src/Agdelte/Theory/`:

| Module | What is proved |
|--------|---------------|
| `AgentCoalg` | `Agent S I O ≅ Coalg (Mono O I)`, `AgentLens = Poly.Lens` (identity) |
| `OpticPolyLens` | `Optic ≅ Poly.Lens` (round-trip proofs) |
| `BigLensPolyLens` | `StatefulBigLens ≅ Coalg (Mono O I)`, `BigLensMap ≅ Poly.Lens`, composition preserved |
| `LensLaws` | `id ∘ f = f`, `f ∘ id = f`, `(f ∘ g) ∘ h = f ∘ (g ∘ h)` for Poly.Lens |
| `SessionDualProof` | `dual (dual s) ≡ s`, `dual` is injective |
| `PolyApp` | `ReactiveApp ↔ Coalg`, signal/app polynomial correspondences |

Since the AgentLens unification, `AgentLens I₁ O₁ I₂ O₂` is definitionally equal to `Lens (Mono O₁ I₁) (Mono O₂ I₂)` — no isomorphism proof needed, it's `refl`.

---

## References

- Spivak, D. "Poly: An abundant categorical setting for mode-dependent dynamics"
- Niu & Spivak "Polynomial Functors: A General Theory of Interaction"
- Riley "Categories of Optics"
- Agda stdlib: `Data.Container` (related but different approach)
