# Agdelte vs Vue 3: Feature Implementation Complexity Analysis

> Feature and approach comparison. Agdelte architecture: [README.md](../README.md)
>
> **Note:** Agdelte uses **ReactiveApp** with templates and bindings (Svelte-style, without Virtual DOM).
> Some examples below use the old `App` with `view` to illustrate patterns — see [api.md](api.md) for the current API.

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

### Update Cycle: O(bindings) vs O(tree)

The fundamental performance difference lies in how DOM updates are computed.

**Vue 3** uses Virtual DOM with optimized diffing:

```
Model change
  → re-run render function → new VNode tree
  → diff(oldTree, newTree) → patches
  → apply patches to real DOM
```

**Agdelte** uses direct reactive bindings (Svelte-style):

```
Model change
  → for each binding: oldVal = extract(oldModel), newVal = extract(newModel)
  → if oldVal !== newVal: update DOM node directly
```

| Metric | Vue 3 | Agdelte |
|--------|-------|---------|
| **Update complexity** | O(tree size) worst case, O(changed subtrees) with block tree optimization | O(number of bindings) |
| **Comparison target** | VNode trees (JS objects) | Extracted values (strings, bools) |
| **Allocation per update** | New VNode tree every render | Zero allocations (in-place comparison) |
| **Static content** | Hoisted at compile time (skipped in diff) | Never touched (only bindings are tracked) |

### Concrete Scenarios

#### Small app (counter: 1 button, 1 text)

| | Vue 3 | Agdelte |
|--|-------|---------|
| Update work | Re-run render → 3 VNodes → diff → 1 patch | 1 binding check → 1 textContent write |
| Overhead | ~minimal (tree is tiny) | ~minimal |
| **Verdict** | **Equal** | **Equal** |

#### Medium app (todo list: 100 items, edit 1)

| | Vue 3 | Agdelte |
|--|-------|---------|
| Update work | Re-run render → ~300 VNodes → diff with keys → 1 patch | ~100 binding checks → 1-3 DOM updates |
| Key optimization | Block tree: skip static parts | Only registered bindings are checked |
| **Verdict** | Fast (block tree) | **Faster** (no tree walk) |

#### Large app (dashboard: 50 components, 1000 bindings, update 1 widget)

| | Vue 3 | Agdelte |
|--|-------|---------|
| Update work | Re-run affected component render → diff subtree → patches | ~1000 binding checks → few DOM updates |
| Key optimization | Component boundaries limit re-render scope | Flat binding list, no tree structure |
| Component isolation | Only changed component re-renders | All bindings checked (no component scoping) |
| **Verdict** | **Faster** (component scoping) | Slower (flat scan of all bindings) |

### Where Agdelte Wins

1. **Fine-grained updates.** Each `bindF` tracks exactly one DOM dependency. No intermediate VNode creation, no diff algorithm. A model change that affects 3 DOM nodes touches exactly 3 nodes.

2. **Zero GC pressure per update.** Vue 3 allocates a new VNode tree on every re-render (even with object pooling, this creates GC work). Agdelte's update loop is allocation-free: compare old/new extracted values, write to DOM if changed.

3. **Predictable latency.** Update time is strictly proportional to the number of bindings. No pathological cases from deep tree diffs or key mismatch.

4. **`when`/`foreach` efficiency.** Conditional blocks (`when`) use a placeholder comment node; toggling is one DOM insert/remove. Keyed lists (`foreachKeyed`) do O(n) reconciliation with data-key attributes — comparable to Vue's keyed v-for.

### Where Vue 3 Wins

1. **Component-scoped reactivity.** Vue's Proxy-based dependency tracking knows *which component* depends on *which data*. Only affected components re-render. Agdelte checks all bindings on every update — no dependency graph to skip irrelevant checks.

2. **Compiler optimizations.** Vue's template compiler marks static hoists, patch flags, and block trees. These reduce diffing work to near-zero for static content. Agdelte's runtime doesn't have this compile-time analysis.

3. **Large apps with many independent components.** When 50 components exist but only 1 changes, Vue re-runs 1 render function. Agdelte scans all 1000 bindings (though each check is a cheap `!==` comparison).

4. **Mature optimizations.** Vue 3 has years of micro-optimization: VNode pooling, Static hoisting, `v-memo`, `v-once`, `KeepAlive` with cached trees. Agdelte's runtime is young.

### Memory

| | Vue 3 | Agdelte |
|--|-------|---------|
| Model storage | Proxy-wrapped reactive objects | Plain JS objects (Scott-encoded) |
| Per-binding overhead | Watcher + dependency sets | `{node, binding}` pair |
| Tree overhead | VNode tree (recreated per render) | None (bindings are flat list) |
| Proxy cost | ~2x memory per reactive object | None |

Agdelte uses less memory per component: no Proxy wrappers, no VNode trees, no Watcher objects. The trade-off is that Scott-encoded Agda data structures can be more verbose than hand-written JS objects.

### Startup Time

| | Vue 3 | Agdelte |
|--|-------|---------|
| Parse + compile | Template compilation (ahead-of-time or runtime) | Agda → JS compilation (ahead-of-time only) |
| First render | Create VNode tree → create DOM | Walk Node tree → create DOM + collect bindings |
| Bundle size | ~30-50 KB gzipped (core + compiler) | ~5-10 KB (reactive.js runtime) |

Agdelte has a smaller runtime footprint. However, compiled Agda modules can be large due to Scott encoding verbosity (each data constructor becomes a function with N branches).

### Theoretical Limits

Both approaches converge to the same theoretical minimum: **O(changed DOM nodes)**. The question is overhead to *identify* which nodes changed:

| | Vue 3 | Agdelte | Svelte |
|--|-------|---------|--------|
| Identify changes via | VNode diff (runtime) | Binding scan (runtime) | Compiled `if (dirty)` checks (compile-time) |
| Overhead | O(tree) → O(blocks) with optimization | O(bindings) | O(dirty flags) — minimal |

Agdelte sits between Vue 3 and Svelte: no tree diffing (like Svelte), but runtime binding scan instead of compile-time dirty flags.

### Summary

| Aspect | Winner | Why |
|--------|--------|-----|
| **Small updates** | Agdelte | Direct binding, zero allocation |
| **Large lists** | Agdelte | O(bindings), no VNode recreation |
| **Many independent components** | Vue 3 | Component-scoped reactivity |
| **Memory usage** | Agdelte | No Proxy, no VNode trees |
| **Bundle size** | Agdelte | ~5 KB vs ~40 KB |
| **Compiled output size** | Vue 3 | Scott encoding is verbose |
| **Worst case latency** | Agdelte | Predictable O(bindings) vs tree diff |
| **Best case latency** | Vue 3 | Skip unchanged components entirely |
| **Maturity** | Vue 3 | Years of micro-optimization |

**Bottom line:** Agdelte matches or beats Vue 3 on small-to-medium apps due to the no-VDOM architecture. Vue 3 has an advantage on large apps with many independent components due to Proxy-based dependency tracking. Both are fast enough for real-world use.

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
