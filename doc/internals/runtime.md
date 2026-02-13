# Agdelte Runtime

JavaScript runtime implementation for Agdelte applications.

## Overview

The runtime interprets Scott-encoded Agda data structures and executes them in the browser. **Key feature: No Virtual DOM** — uses reactive bindings like Svelte.

```
┌──────────────────────────────────────────────────────────────┐
│  Agda                                                        │
│  ReactiveApp { init, update, template }                      │
│  ↓ Compiled to JS (Scott encoding)                           │
├──────────────────────────────────────────────────────────────┤
│  Runtime                                                     │
│  runReactiveApp(app, container)                              │
│  ├─ renderNode(template) — create DOM, track bindings        │
│  ├─ dispatch(msg) — event loop                               │
│  └─ updateScope(scope, old, new) — 3-level optimized update  │
├──────────────────────────────────────────────────────────────┤
│  Update Pipeline                                             │
│  1. Scope cutoff — skip unchanged component subtrees         │
│  2. Slot tracking — skip bindings on unchanged model fields  │
│  3. Cached values — one extract() call, compare with cache   │
│  Result: only touched bindings hit the DOM (NO diffing!)     │
└──────────────────────────────────────────────────────────────┘
```

## Main Loop (Reactive — No VDOM!)

```javascript
function runReactiveApp(app, container) {
  let model = wrapMutable(app.init);  // Wrap for in-place mutation
  const rootScope = createScope();

  // 1. Initial render: create DOM, collect bindings in scopes
  const dom = renderNode(app.template, rootScope);
  container.appendChild(dom);

  // Batched dispatch: collect messages, apply in next animation frame
  function dispatch(msg) {
    batchQueue.push(msg);
    if (!batchScheduled) {
      batchScheduled = true;
      requestAnimationFrame(flushBatch);
    }
  }

  // Immediate dispatch: bypass batching (for keyboard, focus)
  function dispatchSync(msg) {
    const oldModel = model;
    const newModel = app.update(msg)(model);
    model = reconcile(model, newModel);  // In-place mutation
    updateScope(rootScope, oldModel, model);
  }

  function flushBatch() {
    const oldModel = model;
    for (const msg of batchQueue) {
      const newModel = app.update(msg)(model);
      model = reconcile(model, newModel);  // In-place slot updates
    }
    updateScope(rootScope, oldModel, model);  // ONE DOM update for all messages
    batchQueue = [];
  }
}
```

**Key differences from Virtual DOM**:
- No tree reconstruction, no diffing — O(bindings) instead of O(tree)
- Batching: 10 scroll events = 1 DOM update (not 10)
- In-place mutation: model reference stable, only changed slots updated

## Batching (rAF Sync)

Messages are collected within a frame, then applied together:

```
Frame 0: scroll → scroll → scroll → mousemove
         ↓        ↓        ↓         ↓
         batchQueue = [msg1, msg2, msg3, msg4]

requestAnimationFrame →

Frame 1: flushBatch()
         - Apply all 4 messages: model = reconcile(model, update(msg)(model))
         - ONE updateScope() call
         - DOM updated once, synced with browser paint
```

**API:**
- `dispatch(msg)` — batched (default, use for most events)
- `dispatchSync(msg)` — immediate (for keyboard input, focus)

## Scott Encoding

Agda data types compile to functions that pattern match:

```agda
data Cmd A where
  ε : Cmd A
  httpGet : String → (String → A) → (String → A) → Cmd A
```

Compiles to:

```javascript
cmd({
  'ε': () => { /* empty command */ },
  'httpGet': (url, onSuccess, onError) => {
    fetch(url)
      .then(r => r.text())
      .then(text => dispatch(onSuccess(text)))
      .catch(err => dispatch(onError(err.message)));
  }
});
```

**Note:** Agda `Bool` compiles to native JS `true`/`false`, not Scott-encoded.

## In-Place Mutation

Agda models are immutable, but the runtime uses mutable wrappers for efficiency.

### Problem

Every `update(msg)(model)` creates a new model. For large models with blobs
(images, audio buffers), this copies the entire model even if only one field changed.

### Solution: wrapMutable + reconcile

```javascript
// Wrap model with mutable _slots array
function wrapMutable(model) {
  const args = probeSlots(model);   // Extract slots via Proxy
  const ctor = probeCtor(model);    // Extract constructor name
  const slots = args.map(a => typeof a === 'function' ? wrapMutable(a) : a);

  const wrapper = (cases) => cases[ctor](...slots);
  wrapper._slots = slots;  // Same array as in closure!
  wrapper._ctor = ctor;
  return wrapper;
}

// Copy changed slots in-place (uses Agda sharing)
function reconcile(oldModel, newModel) {
  const newSlots = getSlots(newModel);
  for (let i = 0; i < oldModel._slots.length; i++) {
    if (oldModel._slots[i] !== newSlots[i]) {  // Reference comparison
      oldModel._slots[i] = wrapMutable(newSlots[i]);
    }
    // Unchanged slots: same reference → nothing to do
  }
  return oldModel;  // Same reference, mutated
}
```

**Why Agda sharing makes this efficient:**

```javascript
// Agda update returns:
newModel = { time: oldModel.time + 1, audioBuffer: oldModel.audioBuffer }
//                                    ↑ SAME REFERENCE (Agda reuses it)

// reconcile sees:
// slot 0: 0 !== 1 → copy value (4 bytes)
// slot 1: ref === ref → SKIP (100MB untouched!)
```

### Tagged Arrays (Future)

The runtime is prepared for a future compiler format:

```javascript
// Current: Scott-encoded function
model = (cases) => cases["mkModel"](a, b)

// Future: tagged array (naturally mutable)
model = ["mkModel", a, b]

// Runtime handles both via universal accessors:
function getSlots(model) {
  if (isTaggedArray(model)) return model.slice(1);
  if (model._slots) return model._slots;
  return probeSlots(model);
}
```

### SharedArrayBuffer Support

Large data (audio, images) can be stored as SharedArrayBuffer in model slots:

```javascript
// Model slot contains SharedArrayBuffer
model._slots[5] = new Float32Array(new SharedArrayBuffer(44100 * 4));

// On update, reconcile compares by reference:
// - Same buffer → zero work (no copy)
// - Different buffer → copy 8-byte pointer

// Workers can access same buffer (zero-copy):
worker.postMessage({ buffer: model._slots[5].buffer });
```

**User responsibility:** For overlapping SharedArrayBuffer access from multiple
workers, use `Atomics` or ensure non-overlapping ranges.

## Reactive Rendering (No VDOM!)

### renderNode — Initial Render

Walk the template tree, create real DOM, collect bindings:

```javascript
function renderNode(node) {
  return node({
    text: (str) => document.createTextNode(str),

    bind: (binding) => {
      const value = binding.extract(model);
      const textNode = document.createTextNode(value);
      bindings.push({ node: textNode, binding });
      return textNode;
    },

    elem: (tag, attrs, children) => {
      const el = document.createElement(tag);
      // attrs and children are Agda lists — convert via listToArray()
      for (const attr of listToArray(attrs)) applyAttr(el, attr);
      for (const child of listToArray(children)) el.appendChild(renderNode(child));
      return el;
    },

    empty: () => null,

    when: (cond, innerNode) => {
      if (cond(model)) {               // Bool is native JS boolean
        return renderNode(innerNode);
      } else {
        return document.createComment('when');
      }
    },

    foreach: (_typeA, getList, render) => {
      // Note: first arg is implicit Agda type parameter
      const items = listToArray(getList(model));
      items.forEach((item, idx) => {
        container.appendChild(renderNode(render(item)(BigInt(idx))));
      });
    },

    // Keyed list reconciliation
    foreachKeyed: (_typeA, getList, keyFn, render) => {
      // Same key → reuse DOM node; new key → create; removed → destroy
      // Uses data-key attribute for O(n) reconciliation
    },

    // Conditional with CSS transitions
    whenT: (cond, transition, innerNode) => {
      // On enter: add enterClass, render node
      // On leave: add leaveClass, remove after duration ms
    }
  });
}
```

### updateScope — On Model Change

Three-level optimization pipeline:

```
Model change
  │
  ├─ Level 1: Scope cutoff (scopeProj / scope)
  │  If projected sub-model unchanged → skip entire subtree
  │
  ├─ Level 2: Slot-based dependency tracking
  │  Probe model via Proxy → find changed slots (fields)
  │  Skip bindings whose slots didn't change
  │
  └─ Level 3: Cached lastValue comparison
     For affected bindings: extract(newModel), compare with cached value
     Update DOM only if string changed
```

#### Level 1: Scope Cutoff

`zoomNode` wraps each composed component in `scopeProj get`, where `get` is the model projection. On update:

```javascript
// String fingerprint (manual, via `scope`)
if (scope.fingerprint) {
  const newFP = scope.fingerprint(newModel);
  if (newFP === scope.lastFP) return;  // skip entire subtree
}

// Deep structural equality (automatic, via `scopeProj`)
// Fallback for non-record models when slot tracking unavailable
if (scope.project) {
  if (deepEqual(scope.lastProj, scope.project(newModel), 0)) return;
}
```

`deepEqual` handles Scott-encoded records via Proxy introspection: probes both values to extract constructor name + args, compares recursively.

**Depth limit:** `deepEqual` recurses to a maximum of 20 levels (`MAX_DEEP_EQUAL_DEPTH`). Models nested deeper than that fall back to reference equality — bindings may silently stop updating. In practice UI models rarely exceed 4–5 levels, but if you use deeply nested records, flatten them or provide a manual `fingerprint` function.

#### Level 2: Slot-Based Dependency Tracking

Like Vue 3's dependency tracking, but for Scott-encoded records:

```javascript
// 1. Probe model to find changed slots (one Proxy call per update)
const newArgs = probeSlots(newModel);  // model(_slotProbe) → args array
// Compare with cached args from previous update via ===
const changed = new Set();  // indices of changed slots

// 2. Each binding knows its slot dependencies (detected lazily on first update)
//    detectSlots: run extract with each slot replaced by Symbol sentinel
//    If output changes → binding depends on that slot

// 3. Skip bindings whose slots didn't change
for (const b of scope.bindings) {
  if (changed && b.slots && !b.slots.some(s => changed.has(s))) continue;
  // ... extract and update
}
```

Slot detection runs once per binding (lazy, on first update). The static `_slotProbe` Proxy is shared across all calls.

#### Level 3: Cached Last Value

Each binding caches its last extracted string value. Only one `extract(newModel)` call instead of two:

```javascript
const newVal = extract(newModel);
if (newVal !== b.lastValue) {
  b.node.textContent = newVal;
  b.lastValue = newVal;
}
```

#### Performance Summary

For a model with 5 fields and 100 bindings, when 1 field changes:

| Approach | extract calls | DOM checks |
|----------|--------------|------------|
| Naive (old) | 200 (old+new × 100) | 100 |
| With slot tracking | ~20 (affected slot only) | ~20 |
| With scope cutoff (unrelated component) | 0 | 0 |

**Note**: We use JS `!==` instead of Agda's `Binding.equals` because Agda stdlib's string equality (`_≈?_` from Data.String.Properties) causes stack overflow in JS due to deep proof term evaluation.

## Command Execution

Commands are interpreted and executed once:

| Command | Implementation |
|---------|---------------|
| `ε` | No-op |
| `_<>_` | Execute both in parallel |
| `httpGet` | `fetch()` → dispatch result |
| `httpPost` | `fetch()` with POST → dispatch result |
| `attempt` | Execute Task chain → dispatch Result |
| `focus` | `querySelector().focus()` |
| `blur` | `querySelector().blur()` |
| `scrollTo` | `window.scrollTo()` |
| `scrollIntoView` | `querySelector().scrollIntoView()` |
| `writeClipboard` | `navigator.clipboard.writeText()` |
| `readClipboard` | `navigator.clipboard.readText()` → dispatch |
| `getItem` | `localStorage.getItem()` → dispatch Maybe |
| `setItem` | `localStorage.setItem()` |
| `removeItem` | `localStorage.removeItem()` |
| `wsSend` | `ws.send()` (to existing connection) |
| `pushUrl` | `history.pushState()` |
| `replaceUrl` | `history.replaceState()` |
| `back` | `history.back()` |
| `forward` | `history.forward()` |

## Task Execution

Tasks are monadic chains interpreted recursively:

```javascript
function executeTask(task, onSuccess, onError) {
  task({
    'pure': (value) => onSuccess(value),
    'fail': (error) => onError(error),
    'httpGet': (url, onOk, onErr) => {
      fetch(url)
        .then(r => r.text())
        .then(text => executeTask(onOk(text), onSuccess, onError))
        .catch(err => executeTask(onErr(err.message), onSuccess, onError));
    }
  });
}
```

## Subscription Management

### Fingerprint Comparison

Critical optimization for WebSocket and other stateful subscriptions:

```javascript
function serializeEvent(event) {
  return event({
    never: () => 'never',
    interval: (ms, msg) => `interval(${ms})`,
    wsConnect: (url, handler) => `wsConnect(${url})`,
    merge: (e1, e2) => `merge(${serializeEvent(e1)},${serializeEvent(e2)})`,
    // ...
  });
}

function updateSubscriptions() {
  const eventSpec = subs(model);
  const newFingerprint = serializeEvent(eventSpec);

  // Only resubscribe if structure changed
  if (newFingerprint === currentEventFingerprint) return;

  unsubscribe(currentSubscription);
  currentSubscription = interpretEvent(eventSpec, dispatch);
  currentEventFingerprint = newFingerprint;
}
```

### Event Interpretation

Events are AST nodes interpreted by runtime:

| Event | Interpretation |
|-------|---------------|
| `never` | No-op |
| `interval` | `setInterval()` |
| `timeout` | `setTimeout()` |
| `onKeyDown` | `document.addEventListener('keydown')` |
| `onKeyUp` | `document.addEventListener('keyup')` |
| `wsConnect` | `new WebSocket()` with handlers |
| `onUrlChange` | `window.addEventListener('popstate')` |
| `merge` | Interpret both children |
| `debounce` | Wrap inner with debounce logic |
| `throttle` | Wrap inner with throttle logic |
| `foldE` | Maintain internal state; on inner event: `state = step(val, state)`, dispatch state |
| `mapFilterE` | On inner event: apply `f`, dispatch if `just`, skip if `nothing` |
| `switchE` | Subscribe to initial; on meta-event: unsubscribe old, subscribe new |

## Files

| File | Purpose |
|------|---------|
| `runtime/reactive.js` | Main: `runReactiveApp`, `mountReactive`, renderNode, updateBindings |
| `runtime/reactive-auto.js` | Auto-loader: mounts based on `data-agdelte` attribute |
| `runtime/events.js` | interpretEvent, subscribe/unsubscribe |

## Usage

### Auto-loader (recommended)

```html
<div id="app" data-agdelte="Counter"></div>
<script type="module" src="../runtime/reactive-auto.js"></script>
```

### Programmatic

```javascript
import { mountReactive } from './runtime/reactive.js';

await mountReactive('Counter', document.getElementById('app'));

// Custom build directory
await mountReactive('MyApp', '#app', { buildDir: './dist' });
```

### Direct import

```javascript
import { runReactiveApp } from './runtime/reactive.js';
import Counter from './_build/jAgda.Counter.mjs';

await runReactiveApp(Counter, document.getElementById('app'));
```

## See Also

- `doc/todo.md` — future improvements (priority scheduling, time-slicing, workers)
- `doc/ideas/webgl-builder.md` — WebGL builder library design
