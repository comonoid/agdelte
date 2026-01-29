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

Elm Architecture is already a **special case of polynomial machines**:

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

**Current implementation** (Agdelte.Reactive.Node):
```agda
-- Binding tracks reactive connection
record Binding (Model : Set) (A : Set) : Set where
  field
    extract : Model → A
    equals  : A → A → Bool

-- Node is template with bindings
data Node (Model Msg : Set) : Set₁ where
  text : String → Node Model Msg
  bind : Binding Model String → Node Model Msg  -- reactive!
  elem : String → List (Attr Model Msg) → List (Node Model Msg) → Node Model Msg
```

**Advantages over Svelte**:
- (+) Type-safe: bindings verified by Agda
- (+) Explicit: you see what's reactive (`bindF show`)
- (+) No compiler magic: structure is explicit in types
- (+) Same performance: O(bindings), not O(tree)

---

## Phase Planning

> **Priority**: Widget Lenses (eliminating Virtual DOM) is the primary goal.
> Other polynomial applications are secondary and can be deferred.

### Phase 3: Reactive Architecture ✅ DONE

**Focus**: Direct DOM updates through reactive bindings. This is the original Agdelte vision.

```
Agdelte.Reactive.Node    -- Node, Binding, ReactiveApp ✅
```

**Deliverables**:
- [x] `Binding` record with `extract` and `equals`
- [x] `Node` data type with `text`, `bind`, `elem`
- [x] `Attr` with events in attributes (no manual paths!)
- [x] `ReactiveApp` record
- [x] **Demo: ReactiveCounter without Virtual DOM** ✅
- [x] Runtime that tracks bindings and updates DOM directly

**Key insight**: Virtual DOM does `diff(view(oldModel), view(newModel))`.
Reactive bindings do `for each binding: if changed → update DOM node` — no diffing needed.

**Achieved**: Counter demo renders updates without `patch()` function. Same approach as Svelte!

### Phase 4: Proofs & Protocols

**Focus**: Mathematical rigor and protocol examples. Not blocking for Widget Lenses.

```
Agdelte.Poly.Laws        -- Lens laws proofs
Agdelte.Poly.Examples    -- ReqResp, Stream, State protocols
```

**Deliverables**:
- [ ] Prove lens laws in Agda (identity, composition)
- [ ] Coproduct `_⊕_` of polynomials
- [ ] Protocol examples (typed WebSocket, HTTP)

### Phase 5: Agent Networks

**Focus**: Wiring diagrams, multi-agent composition.

```
Agdelte.Poly.Agent       -- Agent coalgebras
Agdelte.Poly.Wiring      -- Wiring diagrams
Agdelte.Poly.Network     -- Network composition
```

**Deliverables**:
- [ ] `Agent` as polynomial coalgebra
- [ ] Wiring diagram DSL
- [ ] Runtime interpreter for networks
- [ ] Demo: Chat system with multiple agents

### Phase 6: Mega-Lens & Navigation

**Focus**: Global state navigation, debugging tools.

```
Agdelte.Poly.MegaLens    -- Global lenses
Agdelte.Poly.Traversal   -- Network traversal
Agdelte.Debug            -- Inspector, time travel
```

**Deliverables**:
- [ ] Focus/zoom into any agent
- [ ] State inspector UI
- [ ] Time-travel debugging
- [ ] Demo: Visual network editor

### Phase 7: Dependent Protocols

**Focus**: Session types, history-dependent protocols.

```
Agdelte.Poly.Dependent   -- Dependent polynomials
Agdelte.Poly.Session     -- Session types
```

**Deliverables**:
- [ ] Dependent polynomial formalization
- [ ] Session type DSL
- [ ] Demo: Multi-step form with typed transitions

---

## Independent Track: Concurrency

> **Note**: Concurrency is orthogonal to the polynomial/lens work.
> Can be developed in parallel with any phase.

**Focus**: Robust handling of async operations and parallel computations.

```
Agdelte.Concurrent.Task    -- Cancellable tasks
Agdelte.Concurrent.Race    -- Race conditions handling
Agdelte.Concurrent.Worker  -- Web Worker integration
```

**Deliverables**:
- [ ] Task cancellation (`cancel : TaskId → Cmd`)
- [ ] Race combinator (`race : Task A → Task A → Task A`)
- [ ] Debounce/throttle at Task level (not just Event)
- [ ] Web Worker offloading for heavy computations
- [ ] Proper error boundaries for concurrent failures

**Current state**: Basic concurrency exists via `Event.merge` and async `Cmd`.
This track extends it with cancellation, racing, and worker support.

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
   - In progress: migrate all examples to ReactiveApp
   - Old VDOM-based examples being replaced

---

## References

- Spivak, D. "Polynomial Functors and Polynomial Monads"
- Niu & Spivak "Polynomial Functors: A General Theory of Interaction"
- Riley "Categories of Optics"
- Agda stdlib: `Data.Container` (related but different approach)
