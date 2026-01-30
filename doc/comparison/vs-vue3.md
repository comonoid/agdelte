# Agdelte vs Vue 3: Feature Implementation Complexity Analysis

> Feature and approach comparison. Agdelte architecture: [README.md](../README.md)
>
> **Note:** Agdelte uses **ReactiveApp** with templates and bindings (Svelte-style, without Virtual DOM).
> Some examples below use the old `App` with `view` to illustrate patterns — see the [API reference](../api/node.md) for the current API.

## Complete List of Required Features

### Core

| Feature | Description |
|------|----------|
| Reactivity | Automatic updates when data changes |
| Conditional rendering | v-if, v-else, v-show |
| Lists | v-for with key for optimization |
| Events | DOM event handling |
| Two-way binding | v-model for forms |
| Computed values | computed, derived data |
| Watchers | watch, reaction to changes |

### Components

| Feature | Description |
|------|----------|
| Props | Passing data to a component |
| Events (emit) | Passing events from a component |
| Slots | Passing content to a component |
| Scoped slots | Slots with access to component data |
| provide/inject | Passing data through the tree without props |
| Async components | Lazy loading of components |
| Dynamic components | Switching components |

### Lifecycle and State

| Feature | Description |
|------|----------|
| Lifecycle hooks | onMounted, onUnmounted, etc. |
| KeepAlive | Preserving state when switching |
| Local state | State inside a component |
| Composables | Reusable logic with state |

### Special Capabilities

| Feature | Description |
|------|----------|
| Teleport | Rendering to another DOM location |
| Transition | Appearance/disappearance animations |
| TransitionGroup | List animations |
| Suspense | Waiting for async components |
| Template refs | Access to DOM elements |
| Custom directives | Custom directives |

### Infrastructure

| Feature | Description |
|------|----------|
| SSR | Server-Side Rendering |
| Hydration | Connecting to SSR markup |
| DevTools | Debugging tools |
| HMR | Hot Module Replacement |
| Scoped CSS | Isolated styles |

---

## Implementation Complexity in Agdelte

### Category A: Trivial (already available or obvious implementation)

| Vue Feature | In Agdelte | Why it's simple |
|----------|-----------|---------------|
| ref/reactive | Signal | This is Signal |
| computed | map, Applicative | `doubled = (2 *_) <$> count` |
| v-if/v-else | if/else in view | Regular code |
| v-show | style display | `style [("display", "none")]` |
| v-for | map | `map viewItem items` |
| v-for :key | key attribute | Add to diff algorithm |
| v-on | onClick, onInput | Already available |
| v-model | value + onInput | Helper: `vmodel msg val` |
| Props | Function arguments | `view : Props → Html Msg` |
| emit | Msg | Returned through onClick, etc. |
| Slots | Html as argument | `card : Html Msg → Html Msg` |
| Scoped slots | Function | `list : (A → Html Msg) → List A → Html Msg` |
| watch | events from Model | `events m = if changed ... then ...` |
| Async components | Event (Html Msg) | Loading as an event |
| Dynamic components | case in view | `case m.tab of ...` |
| KeepAlive | Model stores everything | State is not lost |

**Total: ~16 features — complexity 0-1**

### Category B: Small amount of work (clear how, needs to be written)

| Vue Feature | In Agdelte | Work |
|----------|-----------|--------|
| Keyed diff | Modify diffChildren | Algorithm is known (React/Vue) |
| Teleport | Runtime support | ~50 lines in runtime |
| Transition (CSS) | Runtime + classes | enter/leave classes |
| Suspense | Pattern | `hold fallback asyncContent` |
| provide/inject | Model or implicit args | Choose pattern |

**Total: ~5 features — complexity 2-3**

### Category C: Requires Design

| Vue Feature | In Agdelte | Questions |
|----------|-----------|---------|
| TransitionGroup | FLIP animations | Coordination, FLIP algorithm |
| Scoped CSS | Tooling | Bundler plugin or CSS-in-JS |
| SSR | renderToString + hydrate | Lots of code, algorithms are known |
| DevTools | Browser extension | UI work |
| HMR | Bundler integration | Vite/Webpack plugin |

**Total: ~5 features — complexity 4-6**

---

## Features That SEEM More Complex Due to Architecture

### 1. Component Local State

**Vue:**
```javascript
const localCount = ref(0)  // lives in component
```

**Agdelte:** All state in global Model.

**Seems more complex?** No. It's a different pattern:

```agda
-- Option 1: Nested model
record Model : Set where
  counter1 : ℕ
  counter2 : ℕ

-- Option 2: Map for dynamic components
record Model : Set where
  counters : Map Id ℕ
```

**Elm proved:** Global state works for applications of any size. Helpers are needed (lenses), but that's a library, not architecture.

**Feature implementation complexity: 0** (already works)
**Needed:** Lens library for convenience (~2)

---

### 2. Composables (reusable logic)

**Vue:**
```javascript
function useCounter() {
  const count = ref(0)
  const increment = () => count.value++
  return { count, increment }
}
```

**Agdelte:**
```agda
-- Module with parameterized types
module Counter where
  data Msg = Inc | Dec

  update : Msg → ℕ → ℕ
  update Inc n = suc n
  update Dec n = pred n

  view : ℕ → (Msg → parentMsg) → Html parentMsg
  view n wrap = button [ onClick (wrap Inc) ] [ text "+" ]
```

**More complex?** No. This is a standard functional pattern — modules and higher-order functions.

**Feature implementation complexity: 0** (these are just Agda modules)
**Needed:** Documentation and examples (~1)

---

### 3. Lifecycle hooks (onMounted, onUnmounted)

**Vue:**
```javascript
onMounted(() => console.log('mounted'))
onUnmounted(() => clearInterval(id))
```

**Agdelte:** No explicit lifecycle hooks, but:

```agda
-- onMounted: event on first appearance
events m = if m.justMounted then ... else never

-- onUnmounted: automatic!
-- When events returns never — unsubscription happens
-- Runtime cleans up resources itself
```

**More complex?** SIMPLER! In Vue you need to remember cleanup. In Agdelte cleanup is automatic — Event disappeared from events → unsubscription.

**Complexity: 0** (already works better than in Vue)

---

### 4. Template refs (DOM access)

**Vue:**
```javascript
const inputRef = ref(null)
onMounted(() => inputRef.value.focus())
```

**Agdelte:**
```agda
-- Option 1: via id + Event
input [ id "my-input" ] []

events m = if m.needFocus then focus "my-input" else never

-- Option 2: autofocus attribute (for simple cases)
input [ autofocus ] []
```

**More complex?** Different. Declarative approach instead of imperative.

**Implementation complexity of `focus` primitive: ~1**

---

### 5. Custom directives

**Vue:**
```javascript
app.directive('focus', {
  mounted: (el) => el.focus()
})
```

**Agdelte:** Directives are attributes with special behavior:

```agda
-- v-focus becomes:
autofocus : Attr Msg

-- v-click-outside becomes:
onClickOutside : Msg → Attr Msg
```

**More complex?** No. Each directive is an attribute. There's no "general directive mechanism", but it's not needed — attributes cover all cases.

**Complexity of each "directive": ~1-2**

---

## Conclusion: Are There Features That Are NOTICEABLY Harder?

### Answer: NO

With proper understanding of the architecture, **not a single feature is more complex**. Some are simpler (lifecycle, cleanup). Some are different (local state, composables).

**What looks more complex for the user (not for implementation!):**

| Aspect | Vue | Agdelte |
|--------|-----|---------|
| Add state field | 1 line: `ref(0)` | 3 places: Model, Msg, update |
| Local counter | In component | In global Model |

But this is **usage ergonomics**, not **framework implementation complexity**.

---

## What Is Already Implemented

All categories A and B features are implemented:

- **Core:** ReactiveApp, reactive bindings, events, commands, tasks
- **Incremental updates:** Binding scopes, foreachKeyed, whenT with CSS animations
- **Component composition:** Lens, zoomNode, fstLens/sndLens
- **Combinators & testing:** foldE, mapFilterE, switchE, accumE, mapAccum, pure testing (SimEvent, proofs)
- **Optics:** Prism, Traversal, Affine, unified Optic, zoomNodeL, routeMsg
- **Concurrency:** Agent, Wiring, Session types, ProcessOptic, BigLens, Diagrams

---

## Complexity Comparison

| Category | Number of Features | Complexity |
|-----------|----------------|-----------|
| Trivial | ~16 | 0-1 |
| Small work | ~5 | 2-3 |
| Design | ~5 | 4-6 |

**Key difference from Vue:**

- **Vue:** Need to invent reactivity (Proxy), Virtual DOM, template compiler
- **Agdelte:** Signal/Event — known model from FRP, simpler Runtime, theory (Poly) guarantees correctness

---

## Performance Analysis

### Architecture Comparison

**Vue 3** — Virtual DOM with Proxy-based dependency tracking:

```
Model change
  → Proxy detects which reactive properties changed
  → Re-run render for affected components only
  → diff(oldVNodes, newVNodes) → patches
  → Apply patches to real DOM
```

**Agdelte** — Direct reactive bindings with 3-level optimization:

```
Model change
  → Level 1: Scope cutoff — skip unchanged component subtrees (scopeProj)
  → Level 2: Slot tracking — probe model fields, skip unaffected bindings
  → Level 3: Cached values — one extract() call, compare with cache
  → Update DOM directly (no diffing)
```

| Metric | Vue 3 | Agdelte |
|--------|-------|---------|
| **Change detection** | Proxy on reactive objects (per-property) | Probe Scott-encoded slots (per-field) |
| **Component scoping** | Automatic (Proxy tracks dependencies) | Automatic (zoomNode wraps in scopeProj) |
| **Update complexity** | O(changed components × VNode tree) | O(changed slots × bindings per slot) |
| **Allocation per update** | New VNode tree per component re-render | Zero (in-place comparison with cached values) |
| **Static content** | Hoisted at compile time | Never tracked (only bindings exist) |

### How Agdelte's 3-Level Pipeline Works

#### Level 1: Scope Cutoff (component-level)

`zoomNode` automatically wraps components in `scopeProj`, attaching the projection function. On update, the runtime compares the projected sub-model. If unchanged — entire subtree skipped.

For record models (most common), slot tracking (Level 2) handles this more efficiently. `scopeProj`+`deepEqual` is the fallback for non-record models (e.g., plain `ℕ`).

#### Level 2: Slot-Based Dependency Tracking (field-level)

At first update, the runtime:
1. Probes the model via a static Proxy to extract constructor args (one per field)
2. For each binding, runs `extract` with each slot replaced by a sentinel — if output changes, binding depends on that slot

On subsequent updates:
1. One `probeSlots(newModel)` call — compare args with cached `oldArgs` via `===`
2. Build `changedSlots` set
3. Skip all bindings whose slots aren't in the set

This is analogous to Vue 3's Proxy-based `track()`/`trigger()`, but operates on Scott-encoded Agda records instead of plain JS objects.

#### Level 3: Cached Last Value (binding-level)

Each binding stores its last extracted string value. Only one `extract(newModel)` call needed (not two). DOM update only if value differs from cache.

### Concrete Scenarios

#### Small app (counter: 1 field, 2 bindings)

| | Vue 3 | Agdelte |
|--|-------|---------|
| Update work | Proxy detect → re-render → 3 VNodes → diff → 1 patch | 1 slot probe → 2 cached extract → 1 DOM write |
| **Verdict** | **Equal** | **Equal** |

#### Medium app (todo list: 100 items, edit 1 item text)

| | Vue 3 | Agdelte |
|--|-------|---------|
| Update work | Re-render list component → diff 100 keyed VNodes → 1 patch | Slot `todos` changed → list re-reconciles → 1 item DOM update |
| **Verdict** | Fast (keyed diff) | **Faster** (no VNode tree) |

#### Large app (dashboard: 50 components, 1000 bindings, update 1 widget)

| | Vue 3 | Agdelte |
|--|-------|---------|
| Update work | Proxy detect → 1 component re-render → diff → patches | scopeProj: 49 components skipped. 1 component: slot tracking → ~20 extract calls |
| Component isolation | Proxy tracks per-component deps | zoomNode auto-wraps in scopeProj |
| **Verdict** | **Comparable** | **Comparable** |

This was previously "Vue 3 wins" — before scope cutoff and slot tracking, Agdelte scanned all 1000 bindings. Now it skips 49 unchanged components and only checks bindings in the changed component's slot.

### Where Agdelte Wins

1. **Zero GC pressure per update.** No VNode tree allocation. Agdelte's update is allocation-free: probe slots, compare cached strings, write DOM.

2. **Predictable latency.** O(changed_slots × bindings_per_slot). No pathological deep-tree diffs.

3. **Fine-grained binding.** Each `bindF` tracks one DOM dependency. No intermediate representation.

4. **Smaller runtime.** ~5 KB vs ~40 KB. No template compiler, no VNode infrastructure.

5. **`when`/`foreach` efficiency.** Conditional blocks use comment placeholders. Keyed lists do O(n) reconciliation — comparable to Vue's keyed v-for.

### Where Vue 3 Wins

1. **Deep property tracking.** Vue's Proxy tracks `user.name` separately from `user.age`. Agdelte's slot tracking is top-level only — `user` is one slot. Nested field changes require `zoomNode` composition for equivalent granularity.

2. **Compiler optimizations.** Vue's template compiler produces static hoists, patch flags, block trees. Agdelte has no compile-time template analysis.

3. **Mature micro-optimizations.** VNode pooling, `v-memo`, `v-once`, `KeepAlive` with cached trees. Agdelte's runtime is young.

4. **Ecosystem tooling.** DevTools, SSR, HMR all deeply integrated.

### Scott Encoding: Challenge and Solution

Agda compiles records to Scott-encoded functions. Each field access creates new objects, breaking `===` referential equality. Agdelte solves this with:

- **Slot probing:** a static `Proxy` that intercepts Scott elimination to extract constructor args. One Proxy allocated at module load, reused for all probes.
- **`deepEqual`:** recursive Proxy introspection of Scott-encoded values — used as fallback for non-record models.
- **String fingerprints:** `scope (λ m → show field)` for explicit manual cutoff when needed.

### Memory

| | Vue 3 | Agdelte |
|--|-------|---------|
| Model storage | Proxy-wrapped reactive objects | Plain JS functions (Scott-encoded) |
| Per-binding overhead | Watcher + dependency sets | `{node, binding, lastValue, slots}` |
| Tree overhead | VNode tree (per render) | None (scoped flat lists) |
| Proxy cost | ~2× memory per reactive object | One static Proxy (shared) |

### Startup Time

| | Vue 3 | Agdelte |
|--|-------|---------|
| Parse + compile | Template compilation (AOT or runtime) | Agda → JS (AOT only) |
| First render | Create VNode tree → create DOM | Walk Node tree → create DOM + collect bindings |
| Slot detection | N/A (Proxy wrapping at creation) | Lazy (first update, not first render) |
| Bundle size | ~30-50 KB gzipped | ~5-10 KB |

Slot detection is deferred to the first `dispatch`, so initial render is unaffected.

### Theoretical Position

| | Vue 3 | Agdelte | Svelte |
|--|-------|---------|--------|
| Change detection | Proxy (runtime, per-property) | Slot probe (runtime, per-field) | Compiled dirty flags (compile-time) |
| Scoping | Component-level (Proxy deps) | Component-level (scopeProj) + field-level (slots) | Component-level (compiled) |
| DOM update | VNode diff → patches | Direct DOM write | Direct DOM write |

Agdelte sits between Vue 3 and Svelte: field-level tracking like Vue's Proxy (but via slot probing), direct DOM writes like Svelte (no VDOM).

### Summary

| Aspect | Winner | Why |
|--------|--------|-----|
| **Small updates** | Agdelte | Direct binding, zero allocation |
| **Large lists** | Agdelte | No VNode recreation |
| **Many independent components** | **Comparable** | Both have component-level scoping |
| **Deep property tracking** | Vue 3 | Proxy tracks nested properties; Agdelte needs zoomNode |
| **Memory usage** | Agdelte | No per-object Proxy, no VNode trees |
| **Bundle size** | Agdelte | ~5 KB vs ~40 KB |
| **Compiled output size** | Vue 3 | Scott encoding is verbose |
| **Worst case latency** | Agdelte | Predictable O(slots × bindings/slot) |
| **Maturity** | Vue 3 | Years of micro-optimization |

**Bottom line:** With scope cutoff and slot-based dependency tracking, Agdelte is competitive with Vue 3 across all app sizes. Vue 3 retains an edge in deep property tracking and ecosystem maturity. Agdelte wins on memory, bundle size, and predictable latency. The previous gap on large apps (flat binding scan) is closed by automatic `zoomNode` scoping and field-level slot tracking.

---

## What Agdelte Gets "For Free" from Architecture

| Feature | In Vue | In Agdelte |
|------|-------|-----------|
| Time-travel debugging | Plugin, complex | Trivial (list of Model) |
| Undo/Redo | Write manually | `history[n-1]` |
| State serialization | Complex (Proxy) | `JSON.stringify(model)` |
| Bug reproduction | Complex | Record Msg, replay |
| Testing update | Mocks | `update msg model ≡ expected` |
| Request cancellation | AbortController manually | Automatic |
| Resource cleanup | onUnmounted (easy to forget) | Automatic |
| Race conditions | Possible | Impossible |

---

## Final Answer

### Question: Are there features noticeably harder due to architecture?

**Answer: NO.**

All Vue 3 features are implementable in Agdelte with comparable or less complexity.

### Question: What requires a different approach?

1. **Local state** → Nested models + lenses
2. **Composables** → Modules + higher-order functions
3. **Imperative DOM access** → Declarative Events (focus, blur)
4. **Custom directives** → Attributes

### Question: What requires work (but not due to architecture)?

1. **Tooling:** SSR, DevTools UI, HMR, Scoped CSS
2. **Documentation:** Composition patterns, examples

### Question: Does the correct sequence eliminate complexities?

**YES.** With the correct sequence:
- Each feature builds on previous ones
- No "architectural dead ends"
- Complexity grows linearly, not exponentially

---

## Summary

**Agdelte architecture does not create additional complexity for implementing Vue 3 features.**

- Some features are **simpler** (cleanup, time-travel, request cancellation)
- Some require **different patterns** (local state → nested models)
- All are implementable with **comparable complexity**

**Agdelte advantage:** theoretical foundation (Polynomial Functors) in isolated `Theory/` module guarantees that architecture won't lead to a dead end. Combinators compose correctly by construction.
