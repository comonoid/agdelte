# Polynomial Functors in Agdelte

## Overview

Polynomial functors provide a **unified mathematical framework** for all of Agdelte:

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

**One mechanism for everything:**
- State machines and automata
- Communication protocols
- UI rendering (Widget Lenses — no Virtual DOM!)
- Compositional systems

This document outlines how polynomials form the foundation of Agdelte.

---

## Unified Architecture

### Core Types

```agda
-- Polynomial: interface with outputs and inputs
record Poly : Set₁ where
  field
    Pos : Set           -- positions (what we output)
    Dir : Pos → Set     -- directions (what we accept back)

-- Lens: morphism between polynomials
record Lens (P Q : Poly) : Set where
  field
    onPos : Pos P → Pos Q                      -- forward
    onDir : ∀ p → Dir Q (onPos p) → Dir P p    -- backward

-- Incremental Lens: tracks changes (key for Widget Lenses!)
record IncLens (P Q : Poly) : Set where
  field
    onPos   : Pos P → Pos Q                    -- initial render
    onDelta : ∀ p → ΔPos P → ΔPos Q            -- ⭐ change propagation
    onDir   : ∀ p → Dir Q (onPos p) → Dir P p  -- event handling
```

### Everything is a Lens

| Concept | As Polynomial Lens |
|---------|-------------------|
| **Widget** | `IncLens (ModelPoly M) DOMPoly` |
| **Protocol** | `Lens RequestPoly ResponsePoly` |
| **Component adapter** | `Lens ChildPoly ParentPoly` |
| **Agent** | `Coalgebra P S = S → Σ Pos (Dir → S)` |

### Widget Lenses (The Core Goal)

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

-- The key: onDelta propagates model changes to DOM mutations
-- No diffing needed! The lens structure encodes dependencies.
```

**This is what Svelte does** — but expressed as mathematical structure,
not compiler magic.

---

## Current State (Implicit Polynomials)

The ReactiveApp pattern is already a **special case of polynomial machines**:

```
App Model Msg ≅ P(y) = y^Msg

-- Each message transitions to a new state
-- update : Msg → Model → Model
-- This is a coalgebra of the polynomial y^Msg
```

The `_∥_` composition is the **product of polynomials**:
```
(P × Q)(y) = P(y) × Q(y)
App₁ ∥ App₂ : App (M₁ × M₂) (Msg₁ ⊎ Msg₂)
```

---

## Polynomial Applications

### 1. Explicit Protocol Specification

**Goal**: Type-safe communication between agents.

```agda
-- Polynomial P(y) = Σ (i : Pos) → y^(Dir i)
record Poly : Set₁ where
  field
    Pos : Set           -- positions/states
    Dir : Pos → Set     -- directions from each position

-- Request-Response protocol
ReqResp : Set → Set → Poly
ReqResp Req Resp = record
  { Pos = Req
  ; Dir = λ _ → Resp
  }

-- Streaming protocol
Stream : Set → Poly
Stream A = record
  { Pos = ⊤
  ; Dir = λ _ → A
  }
```

**Use case**: Specifying WebSocket protocols, HTTP APIs, component interfaces.

### 2. Lenses Between Polynomials

**Goal**: Adapters, zooming, refactoring with behavioral preservation.

```agda
-- Morphism P → Q in Poly category
record Lens (P Q : Poly) : Set where
  field
    onPos : Pos P → Pos Q                      -- forward (get)
    onDir : ∀ p → Dir Q (onPos p) → Dir P p    -- backward (set)

-- Identity lens
idLens : ∀ {P} → Lens P P

-- Composition
_∘L_ : Lens Q R → Lens P Q → Lens P R
```

**Use cases**:
- Zoom into sub-component state
- Protocol adapters (e.g., wrap legacy API)
- Refactoring: change internal structure, preserve interface

### 3. Wiring Diagrams (Agent Networks)

**Goal**: Describe topology of communicating agents.

```agda
-- Agent as polynomial coalgebra
Agent : Poly → Set → Set
Agent P S = S → Σ (Pos P) (λ p → Dir P p → S)
--               ^output        ^input → next state

-- Tensor product (parallel composition with interaction)
_⊗_ : Poly → Poly → Poly

-- Coproduct (choice)
_⊕_ : Poly → Poly → Poly

-- Wiring: connect output of P to input of Q
wire : (f : Pos P → Dir Q _) → Agent P S → Agent Q S → Agent (P ⊗ Q) S
```

**Use case**: Multi-agent systems, microservices topology, game entities.

### 4. Mega-Lens (Global System Navigation)

**Goal**: Navigate and modify entire agent network.

```agda
-- Global state as product of local states
record Network : Set₁ where
  field
    agents : List (Σ Poly (λ P → Σ Set (Agent P)))
    wiring : WiringDiagram agents

-- Lens to focus on specific agent
focus : (i : Fin n) → Lens Network (agents !! i)

-- Traverse and modify
over : Lens Network A → (A → A) → Network → Network
```

**Use case**: Debugging, state inspection, hot reloading, time travel.

### 5. Dependent Protocols

**Goal**: Protocols that depend on history/context.

```agda
-- Protocol depends on interaction history
DepPoly : Set → Set₁
DepPoly H = Σ (Pos : H → Set) (λ P → (h : H) → P h → Set)

-- Session types as dependent polynomials
Session : DepPoly History
```

**Use case**: Session types, stateful protocols, authentication flows.

### 6. Widget Lenses (Original Vision!)

> **This was the original motivation for Agdelte!**
>
> The name **Agdelte = Agda + Svelte** reflects the goal:
> achieve Svelte's direct DOM updates through dependent types and lenses.

**Goal**: Build UI without Virtual DOM diffing — like Svelte, but with type-safe lenses.

**How Svelte does it**:
```js
// Svelte compiles declarative template to direct mutations:
if (changed.count) {
  set_data(t, count);  // direct update, no diffing
}
// The "correct structure" of the template enables this
```

**How Agdelte could do it**:
```agda
-- Widget as lens into DOM
Widget : Set → Set → Set
Widget Model View = Lens (Const Model) (DOM View)

-- The lens structure tells us exactly what to update
-- Model change → lens path → direct DOM mutation

-- Composition preserves update paths
_>>>_ : Widget A B → Widget B C → Widget A C

-- Direct DOM updates through lens, no diffing needed
update : Widget M V → ΔModel → DOM → DOM
update widget δm dom = over (widget .onDir) δm dom
```

**Key insight**: The "correct structure" that Svelte extracts from templates
can be expressed as **polynomial lenses** in Agda. Dependent types ensure
the structure is always correct.

**Why we moved away from Virtual DOM**:
- Virtual DOM was only a temporary solution
- Same performance characteristics as Svelte now achieved!
- Direct DOM updates via reactive bindings

**Current implementation**: See [api.md](api.md) for full ReactiveApp/Node/Binding API.

**Advantages over Svelte**:
- (+) Type-safe: bindings verified by Agda
- (+) Explicit: you see what's reactive (`bindF show`)
- (+) No compiler magic: structure is explicit in types
- (+) Same performance: O(bindings), not O(tree)

---

## Phase Planning

> **Priority**: Widget Lenses (eliminating Virtual DOM) is the primary goal.
> Other polynomial applications are secondary and can be deferred.

### Phase 2: Reactive Architecture ✅ DONE

**Focus**: Direct DOM updates through reactive bindings. This is the original Agdelte vision.

**Deliverables** (all complete):
- [x] `Binding` record with `extract` and `equals`
- [x] `Node` data type with `text`, `bind`, `elem`, `empty`, `when`, `foreach`
- [x] `Attr` with events in attributes (no manual paths!)
- [x] `ReactiveApp` record, `zoomNode` composition
- [x] All 12 examples using ReactiveApp
- [x] Runtime with direct DOM updates (no VDOM)

See [architecture.md](architecture.md) for full API details.

### Phase 3: Incremental Updates ✅ DONE

**Focus**: Efficient dynamic lists and conditional rendering.

**Deliverables**:
- [x] Keyed `foreach` — `foreachKeyed` with key-based reconciliation
- [x] Binding scopes — each `when`/`foreach` block gets its own scope
- [x] `whenT` with CSS enter/leave animations via `Transition` record

### Phase 4: Widget Lenses ✅ DONE

**Focus**: Full lens-based model navigation within widgets.

**Deliverables**:
- [x] `Lens Outer Inner` with get/set/modify
- [x] Lens composition `_∘L_`
- [x] `fstLens`, `sndLens` — product lenses
- [x] `zoomNode` — maps both model AND messages

### Phase 5: Combinators and Testing ✅ DONE

**Focus**: Event combinators and pure testing. See [combinators.md](combinators.md).

**Deliverables**:
- [x] `foldE`, `mapFilterE`, `switchE` — stateful combinators
- [x] `accumE`, `mapAccum` — derived combinators
- [x] Pure testing: `SimEvent`, `interpretApp`, 6 proofs

### Phase 6: Optics + Widget Networks ✅ DONE

**Focus**: Optics hierarchy and typed widget composition.

**Deliverables**:
- [x] `Prism`, `Traversal`, `Affine`, unified `Optic` with `_∘O_`
- [x] `zoomNodeL` — typed component composition with Lens + Prism
- [x] `routeMsg` — automatic message routing via Prism
- [x] 16 propositional equality proofs in OpticTest

### Phase 7: Concurrency + Protocols

**Focus**: Workers as agents in polynomial network, typed communication.

**Deliverables**:
- [ ] `Agent` as polynomial coalgebra
- [ ] Workers as agents (channels = Dir of polynomial)
- [ ] Protocol Lens — typed agent communication
- [ ] Structured concurrency via wiring
- [ ] parallel, race, cancellation
- [ ] Demo: Chat system with multiple agents

### Phase 8: Developer Experience

**Focus**: DevTools powered by Big Lens.

**Deliverables**:
- [ ] Network inspector via Big Lens
- [ ] Time-travel debugging
- [ ] Hot reload

### Phase 9: Formal Properties + Session Types

**Focus**: Mathematical rigor, dependent protocols.

**Deliverables**:
- [ ] Lens laws proofs (identity, composition)
- [ ] ReactiveApp ↔ Coalg formal connection
- [ ] Dependent polynomial formalization
- [ ] Session type DSL
- [ ] Demo: Multi-step form with typed transitions

---

## Open Questions (Many Resolved!)

1. **Widget Lenses**: How to represent "model delta" generically?
   - ✅ **RESOLVED**: Use `Binding` with `extract` and `equals`
   - Runtime checks `equals(extract(old), extract(new))` for each binding

2. **Performance**: Can lens interpretation match Virtual DOM speed?
   - ✅ **RESOLVED**: Yes! O(bindings) is faster than O(tree)
   - Same approach as Svelte's compiled output

3. **Ergonomics**: Will lens-based views be as readable as current `Html Msg`?
   - ✅ **RESOLVED**: `bindF show` is clean and declarative
   - Events in attributes: `onClick Dec` — no manual paths!

4. **Migration**: How to incrementally adopt Widget Lenses?
   - ✅ **RESOLVED**: All 9 examples migrated to ReactiveApp
   - Old VDOM-based code removed

---

## References

- Spivak, D. "Polynomial Functors and Polynomial Monads"
- Niu & Spivak "Polynomial Functors: A General Theory of Interaction"
- Riley "Categories of Optics"
- Agda stdlib: `Data.Container` (related but different approach)
