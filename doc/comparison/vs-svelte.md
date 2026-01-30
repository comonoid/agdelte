# Svelte 5 vs Agdelte: Example Comparison

> Detailed comparison of approaches. Agdelte Architecture: [README.md](../README.md)
>
> **Key similarity:** Both Svelte and Agdelte use **direct DOM updates without Virtual DOM**.
> The difference is that Svelte achieves this through compilation, while Agdelte uses explicit bindings.
>
> **Note:** Examples below use **ReactiveApp** (template with bindings).
> For the full API see the [API reference](../api/node.md).

11 examples with analysis of advantages and disadvantages of both approaches.

---

## 1. Counter (basic reactivity)

### Svelte 5

```svelte
<script>
  let count = $state(0)
</script>

<button onclick={() => count++}>
  Clicked {count} times
</button>
```

### Agdelte

```agda
data Msg = Inc

template : Node ℕ Msg
template = button [ onClick Inc ] [ bindF (λ n → "Clicked " ++ show n ++ " times") ]

app = mkReactiveApp 0 (λ { Inc n → suc n }) template
```

### Analysis

| | Svelte | Agdelte |
|--|--------|---------|
| **Conciseness** | ✅ 5 lines | ✅ 4 lines |
| **DOM updates** | ✅ Direct (compiler) | ✅ Direct (bindings) |
| **Type system** | ⚠️ TypeScript (optional) | ✅ Dependent types |
| **Virtual DOM** | ❌ No | ❌ No |

**Common:** Both use direct DOM updates without diffing!

**Svelte:** Compiler generates update code.

**Agdelte:** `bindF` explicitly indicates what gets updated.

---

## 2. Two-way binding (input)

### Svelte 5

```svelte
<script>
  let name = $state('')
</script>

<input bind:value={name} />
<p>Hello, {name}!</p>
```

### Agdelte

```agda
data Msg = SetName String

template : Node String Msg
template = div []
  ( input (vmodel id SetName) []
  ∷ p [] [ bindF (λ name → "Hello, " ++ name ++ "!") ]
  ∷ [] )

app = mkReactiveApp "" (λ { (SetName s) _ → s }) template
```

### Analysis

| | Svelte | Agdelte |
|--|--------|---------|
| **Syntax** | ✅ `bind:value` — one line | ✅ `vmodel getText SetText` — one line |
| **Data direction** | ⚠️ Bidirectional (magic) | ✅ Unidirectional (explicit) |
| **Debugging** | ⚠️ Harder to track source | ✅ Always visible where data comes from |
| **Validation** | ⚠️ Needs separate `$effect` | ✅ Natural in `update` |

**Svelte better:** ergonomics for simple forms.

**Agdelte better:** complex forms with validation, debugging data flow.

---

## 3. Derived values

### Svelte 5

```svelte
<script>
  let items = $state([1, 2, 3, 4, 5])
  let total = $derived(items.reduce((a, b) => a + b, 0))
  let average = $derived(total / items.length)
</script>

<p>Total: {total}, Average: {average}</p>
```

### Agdelte

```agda
record Model : Set where
  field items : List ℕ

-- Derived values are just functions
total : Model → ℕ
total m = sum (m .items)

average : Model → ℕ
average m = total m / length (m .items)

template : Node Model Msg
template = p []
  [ bindF (λ m → "Total: " ++ show (total m) ++ ", Average: " ++ show (average m)) ]
```

### Analysis

| | Svelte | Agdelte |
|--|--------|---------|
| **Syntax** | ✅ `$derived` — declarative | ✅ Just functions |
| **Memoization** | ✅ Automatic | ✅ Not needed: `bindF` checks `equals(old, new)` and updates DOM only on change |
| **Composition** | ⚠️ Only in component | ✅ Regular functions, easy to test |
| **Dependencies** | ⚠️ Tracked at runtime | ✅ Explicit (function arguments) |

**Svelte better:** automatic memoization, less code.

**Agdelte better:** derived values are regular functions, easy to test and reuse.

---

## 4. Effects (side effects)

### Svelte 5

```svelte
<script>
  let count = $state(0)

  $effect(() => {
    console.log('Count changed:', count)
    document.title = `Count: ${count}`
  })
</script>
```

### Agdelte

```agda
-- Effects not inside component!
-- Logging — through middleware in runtime
-- document.title — through special Event

data Msg = Inc | SetTitle String

app = record
  { ...
  ; update = λ where
      Inc m → record m { count = suc (m .count); needTitleUpdate = true }
      (SetTitle _) m → record m { needTitleUpdate = false }

  ; events = λ m →
      if m .needTitleUpdate
      then mapE SetTitle (setDocumentTitle ("Count: " ++ show (m .count)))
      else never
  }

-- Or: title as part of view (declarative)
-- view m = { body = ..., title = "Count: " ++ show (m.count) }
```

### Analysis

| | Svelte | Agdelte |
|--|--------|---------|
| **Simplicity** | ✅ `$effect` — one construct | ❌ Need separate Event primitive |
| **Purity** | ❌ Effects everywhere | ✅ Effects only in events |
| **Predictability** | ⚠️ When will it execute? | ✅ Explicit: when Event is active |
| **Testing** | ❌ Need mock DOM | ✅ update is pure, effects isolated |

**Svelte better:** quick integration with imperative code.

**Agdelte better:** all effects are explicit, easier to debug and test.

---

## 5. Conditional rendering

### Svelte 5

```svelte
<script>
  let loggedIn = $state(false)
</script>

{#if loggedIn}
  <Dashboard />
{:else}
  <LoginForm />
{/if}
```

### Agdelte

```agda
template : Node Model Msg
template = div []
  ( when loggedIn (zoomNode user DashMsg dashboardTemplate)
  ∷ when (not ∘ loggedIn) loginTemplate
  ∷ [] )
```

### Analysis

| | Svelte | Agdelte |
|--|--------|---------|
| **Syntax** | ✅ `{#if}` — readable template | ✅ Regular `if-then-else` |
| **Nesting** | ⚠️ `{:else if}` — verbose | ✅ `case`, pattern matching |
| **Type safety** | ⚠️ Runtime checks | ✅ Compile-time |
| **Exhaustiveness** | ❌ No checking | ✅ Agda checks all cases |

**Svelte better:** visually closer to HTML.

**Agdelte better:** pattern matching, exhaustiveness checking.

---

## 6. Lists

### Svelte 5

```svelte
<script>
  let todos = $state([
    { id: 1, text: 'Learn Svelte', done: false },
    { id: 2, text: 'Build app', done: false }
  ])
</script>

<ul>
  {#each todos as todo (todo.id)}
    <li class:done={todo.done}>
      {todo.text}
    </li>
  {/each}
</ul>
```

### Agdelte

```agda
template : Node Model Msg
template = ul []
  [ foreach todos (λ t _ →
      li [ classBind (λ _ → if done t then "done" else "") ]
        [ text (todoText t) ]
    ) ]
```

### Analysis

| | Svelte | Agdelte |
|--|--------|---------|
| **Syntax** | ✅ `{#each}` with destructuring | ✅ `map` — standard function |
| **Keyed lists** | ✅ `(todo.id)` built-in | ✅ `foreachKeyed` |
| **Performance** | ✅ Optimized diff | ✅ Keyed reconciliation — O(1) per change |
| **Readability** | ✅ Template similar to HTML | ✅ Functional style |

**Svelte better:** keyed lists out of the box, familiar syntax.

**Agdelte better:** `map` — universal function, works everywhere.

---

## 7. Data loading (fetch)

### Svelte 5

```svelte
<script>
  let data = $state(null)
  let loading = $state(false)
  let error = $state(null)

  async function loadData() {
    loading = true
    error = null
    try {
      const res = await fetch('/api/data')
      data = await res.json()
    } catch (e) {
      error = e.message
    } finally {
      loading = false
    }
  }
</script>

<button onclick={loadData} disabled={loading}>
  {loading ? 'Loading...' : 'Load Data'}
</button>

{#if error}
  <p class="error">{error}</p>
{/if}

{#if data}
  <pre>{JSON.stringify(data, null, 2)}</pre>
{/if}
```

### Agdelte

```agda
data Status = Idle | Loading | Success Data | Failure String

data Msg = LoadData | GotData String | GotError String

update : Msg → Model → Model
update LoadData m = record m { status = Loading }
update (GotData d) m = record m { status = Success (parse d) }
update (GotError e) m = record m { status = Failure e }

template : Node Model Msg
template = div []
  ( button [ onClick LoadData, disabledBind isLoading ]
      [ bindF (λ m → if isLoading m then "Loading..." else "Load Data") ]
  ∷ when isFailure (p [ class "error" ] [ bindF showError ])
  ∷ when isSuccess (pre [] [ bindF showData ])
  ∷ [] )

cmd : Msg → Model → Cmd Msg
cmd LoadData _ = httpGet "/api/data" GotData GotError
cmd _ _ = ε

app = mkReactiveApp initModel update template
```

### Analysis

| | Svelte | Agdelte |
|--|--------|---------|
| **Number of states** | ⚠️ 3 variables (data, loading, error) | ✅ 1 ADT (Status) |
| **Impossible states** | ❌ `loading=true, data=X` possible | ✅ Excluded by type |
| **Request cancellation** | ❌ Need AbortController manually | ✅ Automatic (remove from events) |
| **Boilerplate** | ⚠️ try/catch/finally | ⚠️ Explicit pattern matching |
| **Retries** | ❌ Manual | ✅ Just stay in Loading |

**Svelte better:** familiar async/await, less code for simple cases.

**Agdelte better:** impossible states excluded by types, automatic cancellation.

---

## 8. Components and props

### Svelte 5

```svelte
<!-- Button.svelte -->
<script>
  let { label, disabled = false, onclick } = $props()
</script>

<button {disabled} {onclick}>{label}</button>

<!-- Parent.svelte -->
<script>
  import Button from './Button.svelte'
</script>

<Button label="Click me" onclick={() => alert('clicked')} />
```

### Agdelte

```agda
-- Button as a function
button' : String → Bool → Msg → Html Msg
button' label disabled msg =
  button [ onClick msg, disabled disabled ] [ text label ]

-- Or as a parameterized module
module Button (Msg : Set) where
  record Props : Set where
    field
      label    : String
      disabled : Bool
      onClick  : Msg

  view : Props → Html Msg
  view p = button [ onClick (p .onClick), disabled (p .disabled) ]
    [ text (p .label) ]

-- Usage
view m = div []
  [ Button.view (record { label = "Click me"; disabled = false; onClick = Clicked })
  ]
```

### Analysis

| | Svelte | Agdelte |
|--|--------|---------|
| **Encapsulation** | ✅ .svelte file = component | ✅ Module = component |
| **Props typing** | ⚠️ TypeScript (optional) | ✅ Record with types |
| **Default props** | ✅ `= false` in destructuring | ⚠️ Need wrapper function |
| **Simple cases** | ✅ Component not needed | ✅ Just a function |

**Svelte better:** file system as structure, default props.

**Agdelte better:** components are regular functions/modules, unified typing.

---

## 9. Events between components

### Svelte 5

```svelte
<!-- Child.svelte -->
<script>
  import { createEventDispatcher } from 'svelte'
  const dispatch = createEventDispatcher()
</script>

<button onclick={() => dispatch('select', { id: 42 })}>
  Select
</button>

<!-- Parent.svelte -->
<script>
  function handleSelect(e) {
    console.log('Selected:', e.detail.id)
  }
</script>

<Child on:select={handleSelect} />
```

### Agdelte

```agda
-- Child
module Child where
  data Msg = Select ℕ

  view : Html Msg
  view = button [ onClick (Select 42) ] [ text "Select" ]

-- Parent
module Parent where
  data Msg = ChildMsg Child.Msg | Other

  update : Msg → Model → Model
  update (ChildMsg (Child.Select id)) m = handleSelect id m
  update Other m = ...

  view : Model → Html Msg
  view m = div []
    [ mapHtml ChildMsg Child.view  -- Msg transformation
    ]
```

### Analysis

| | Svelte | Agdelte |
|--|--------|---------|
| **Mechanism** | ⚠️ Separate dispatch API | ✅ Just types (Msg) |
| **Event typing** | ❌ `e.detail` — any | ✅ `Child.Select ℕ` |
| **Bubbling** | ⚠️ Through `on:select` | ✅ Explicit `mapHtml` |
| **Handling** | ⚠️ Callback in template | ✅ Centralized in update |

**Svelte better:** familiar DOM event model.

**Agdelte better:** type safety, all handlers in one place (update).

---

## 10. Global state (stores)

### Svelte 5

```svelte
<!-- stores.js -->
import { writable } from 'svelte/store'
export const user = writable(null)
export const theme = writable('light')

<!-- Component.svelte -->
<script>
  import { user, theme } from './stores'
</script>

<p>User: {$user?.name}</p>
<button onclick={() => $theme = $theme === 'light' ? 'dark' : 'light'}>
  Toggle theme
</button>
```

### Agdelte

```agda
-- All state in one Model
record Model : Set where
  field
    user  : Maybe User
    theme : Theme
    ...   -- rest of application state

data Msg = SetUser (Maybe User) | ToggleTheme | ...

-- Global state = App Model
app : App Msg Model
app = record
  { init = { user = Nothing; theme = Light; ... }
  ; update = λ where
      (SetUser u) m → record m { user = u }
      ToggleTheme m → record m { theme = toggle (m .theme) }
      ...
  ; ...
  }

-- Access in any view through Model
viewHeader : Model → Html Msg
viewHeader m = div []
  [ text ("User: " ++ maybe "Guest" name (m .user))
  , button [ onClick ToggleTheme ] [ text "Toggle theme" ]
  ]
```

### Analysis

| | Svelte | Agdelte |
|--|--------|---------|
| **Modularity** | ✅ Separate stores | ⚠️ One big Model |
| **Reactivity** | ✅ Auto-subscription via `$` | ✅ view receives entire Model |
| **Consistency** | ⚠️ Stores independent | ✅ All state atomic |
| **Time-travel debug** | ❌ Difficult | ✅ Easy (one Model) |
| **Selectors** | ⚠️ derived stores | ✅ Just functions `Model → A` |

**Svelte better:** modularity, independent stores for different parts.

**Agdelte better:** single source of truth, atomic updates, time-travel debugging.

---

## 11. Animations (animationFrame)

### Svelte 5

```svelte
<script>
  import { onMount, onDestroy } from 'svelte'

  let position = $state(0)
  let velocity = 200  // px/sec
  let rafId
  let lastTime

  function animate(time) {
    if (lastTime) {
      const dt = time - lastTime
      position += velocity * dt / 1000
    }
    lastTime = time
    rafId = requestAnimationFrame(animate)
  }

  onMount(() => {
    rafId = requestAnimationFrame(animate)
  })

  onDestroy(() => {
    cancelAnimationFrame(rafId)
  })
</script>

<div style="transform: translateX({position}px)">●</div>
```

### Agdelte

```agda
data Msg = Tick FrameInfo | ToggleAnimation

record Model : Set where
  field
    position  : ℕ
    velocity  : ℕ
    animating : Bool

update : Msg → Model → Model
update (Tick frame) m = record m
  { position = m .position + m .velocity * frame .dt / 1000 }
update ToggleAnimation m = record m { animating = not (m .animating) }

template : Node Model Msg
template = div [ styleBind "transform" (λ m → "translateX(" ++ show (m .position) ++ "px)") ]
  [ text "●" ]

subs : Model → Event Msg
subs m = if m .animating
  then mapE Tick animationFrame  -- browser provides dt and fps
  else never                      -- automatic RAF cancellation

app = mkReactiveApp initModel update template
```

### Analysis

| | Svelte | Agdelte |
|--|--------|---------|
| **RAF management** | ⚠️ Manual (onMount/onDestroy) | ✅ Automatic (events) |
| **Delta time** | ⚠️ Calculate manually | ✅ Ready `frame.dt` |
| **FPS** | ❌ No | ✅ Ready `frame.fps` |
| **Cleanup** | ⚠️ Can forget cancelAnimationFrame | ✅ Automatic with `never` |
| **Animation pause** | ⚠️ Flags, conditions in animate | ✅ `if animating then ... else never` |

**Svelte better:** familiar imperative approach.

**Agdelte better:** declarative animation control, automatic cleanup, built-in dt/fps.

---

## Summary Table

| Aspect | Svelte 5 | Agdelte |
|--------|----------|---------|
| **Learning curve** | ✅ Low | ⚠️ Requires Agda |
| **Boilerplate** | ✅ Minimal | ⚠️ More code |
| **Type safety** | ⚠️ Optional | ✅ Built-in |
| **Testability** | ⚠️ Need mocks | ✅ Pure functions |
| **Predictability** | ⚠️ Implicit reactivity | ✅ Explicit data flow |
| **Performance** | ✅ Optimized | ⚠️ Depends on implementation |
| **Ecosystem** | ✅ Rich | ❌ New |
| **Tooling** | ✅ DevTools, HMR | ⚠️ Basic |

---

## When to choose what

### Svelte better for:
- Rapid prototyping
- Small projects
- Teams without FP experience
- Integration with existing JS code
- When ecosystem and tooling matter

### Agdelte better for:
- Critical applications (finance, medicine)
- Complex business logic
- When formal guarantees are needed
- Teams with FP experience
- Long-lived projects with high quality requirements
- Learning FRP and dependent types

---

## Philosophical difference

### Common: No Virtual DOM!

Both Svelte and Agdelte abandoned Virtual DOM in favor of direct DOM updates:

| | Virtual DOM (React/Elm) | Svelte | Agdelte |
|--|-------------------------|--------|---------|
| How DOM is updated | diff(oldTree, newTree) → patches | Compiler generates `if (changed.x)` | `bindF` tracks changes |
| Performance | O(tree size) | O(changed bindings) | O(changed bindings) |
| When analysis happens | Runtime | Compile time | Runtime (explicit bindings) |

### Difference: Magic vs Explicitness

**Svelte:** "Make it simple, compiler will figure it out"
- Compiler analyzes template and generates optimal updates
- User doesn't see how it works
- Reactivity is a compiler feature

**Agdelte:** "Make it explicit, types guarantee"
- `bindF show` explicitly says: "this place depends on model"
- User sees all reactive connections
- Reactivity is an explicit data structure

### Three layers of Agdelte

```
┌─────────────────────────────────────────────────────────┐
│  Level 3: Declarative DSL                               │
│  button [ onClick Dec ] [ bindF show ]                 │
│  Svelte-like syntax, explicit bindings                  │
├─────────────────────────────────────────────────────────┤
│  Level 2: Lenses                                        │
│  Navigation, modification, composition                  │
│  Runtime flexibility                                    │
├─────────────────────────────────────────────────────────┤
│  Level 1: Polynomials (Theory/)                         │
│  Mathematical foundation                                │
│  Formal guarantees, proofs                              │
└─────────────────────────────────────────────────────────┘
```

Svelte and Agdelte arrived at the same solution (No VDOM) through different paths:
- Svelte — through compiler analysis
- Agdelte — through explicit bindings with types
