# In-place mutation for lenses at the JS runtime level

## Problem

Agdelte models are immutable. Every `Lens.set` creates a new copy of the
outer structure. For small models (counters, forms) this is free. For large
models containing blobs (images, audio buffers, large arrays) every `dispatch`
copies the entire model even if only a tiny field changed.

Example: model is `(ImageData, Brightness)`. User drags a brightness slider.
Agda's compiled `fstLens.set` does `(newImg, b)` -- allocates a new pair and
copies the reference to ImageData. For a flat pair this is cheap, but for
deeply nested records with large sub-trees the copying cascades through every
level of nesting.

The key insight: the optimisation belongs in `runtime/reactive.js`, not in
Agda's compiler output. The Agda side stays pure; the JS runtime is free to
implement `set` as in-place mutation.

## Current architecture (what to preserve)

### Dispatch cycle (`runtime/reactive.js:299-334`)

```javascript
function dispatch(msg) {
  const oldModel = model;
  model = update(msg)(oldModel);          // Agda-compiled, returns NEW object
  updateScope(rootScope, oldModel, model); // compares old vs new
}
```

### Binding update (`runtime/reactive.js:591-662`)

Each binding stores `lastValue` -- the previously extracted string. On update:

```javascript
const newVal = extract(newModel);
if (newVal !== b.lastValue) {
  b.node.textContent = newVal;   // direct DOM mutation
  b.lastValue = newVal;
}
```

This compares `lastValue` (cached string) with `extract(newModel)` (fresh
extraction). It does NOT compare `oldModel` with `newModel` directly.
**Binding update already survives in-place mutation.**

### Slot-based scope optimisation (`runtime/reactive.js:147-219`)

This is the part that BREAKS under mutation. The mechanism:

1. `countSlots(model)` -- probes the Scott-encoded model via Proxy to count
   how many constructor arguments (slots) it has.

2. `probeSlots(model)` -- calls `model(_slotProbe)` where `_slotProbe` is a
   Proxy that returns the raw constructor arguments as an array. This gives
   `[slot0, slot1, ..., slotN]` -- the actual JS values in each field.

3. `changedSlotsFromCache(scope, newModel)` -- probes `newModel`, compares
   each slot with the cached probe from last update via `===` (reference
   equality). Returns a `Set` of changed slot indices.

4. If no slots changed, the entire scope is skipped. If some changed, only
   bindings whose `detectSlots` dependency list intersects the changed set
   are re-evaluated.

**Why it breaks:** `probeSlots` extracts references. If the model was mutated
in-place, `oldArgs[i] === newArgs[i]` is trivially true for every slot because
they point to the same object. The optimisation concludes "nothing changed" and
skips all updates.

### Fingerprint / deepEqual fallback (`runtime/reactive.js:593-613`)

```javascript
if (scope.fingerprint) {
  const newFP = scope.fingerprint(newModel);
  if (newFP === scope.lastFP) return;
  scope.lastFP = newFP;
}
// ...
if (scope.project) {
  const newProj = scope.project(newModel);
  if (deepEqual(scope.lastProj, newProj, 0)) return;
  scope.lastProj = newProj;
}
```

`fingerprint` is a `Model -> String` function from `scope` nodes. It would
still work under mutation (re-extracts every time). `deepEqual` on
`scope.lastProj` would also fail if the projection returns the same reference.

## Proposed design: Ref-based in-place mutation

### Core idea

Lenses return **references** (slot pointers) instead of values. A reference
is `{target: parentSlots, idx: slotIndex}`. The `set` operation writes
directly to `ref.target[ref.idx]` — true in-place mutation with no copying
of unchanged parts.

### Why this works for all data types

**Primitives (numbers, booleans):**
- Stored directly in slot
- `ref.target[ref.idx] = 42` — replaces value in-place

**Strings:**
- Immutable in JS, but that's fine
- `ref.target[ref.idx] = "new"` — replaces pointer, structure unchanged
- Externally looks like in-place update

**Large arrays:**
- Array reference in slot: `_slots[5] = hugeArray`
- Changing another slot → array untouched (no copy!)
- Replacing array → `_slots[5] = newArray` (pointer swap)
- Mutating inside → `_slots[5][i] = x` (even faster, true in-place)

**Nested records:**
- Path: `model.user.settings.theme`
- `locate` traverses: `model._slots[0]._slots[2]._slots[1]`
- Returns ref to final slot
- Intermediate structures NOT recreated!

### Step 1: Mutable model wrapper

Wrap Scott-encoded models so slots are accessible and mutable:

```javascript
function wrapMutable(model) {
  if (model._slots) return model;  // already wrapped

  const args = probeSlots(model);   // [slot0, slot1, ...]
  const ctor = probeCtor(model);    // constructor name

  // Recursively wrap nested structures
  const slots = args.map(a =>
    typeof a === 'function' ? wrapMutable(a) : a
  );

  // Create wrapper with mutable slots
  const wrapper = (cases) => cases[ctor](...slots);
  wrapper._slots = slots;
  wrapper._ctor = ctor;
  return wrapper;
}
```

Key insight: `wrapper._slots` is the **same array** closed over by the
function. Mutating `_slots[i]` changes what `wrapper(cases)` returns!
```

### Step 2: Reconcile — the core operation

Current Agda lenses are pure get/set records. Two integration paths:

**Path A — Runtime interception (minimal Agda changes):**
1. Agda `update` still returns "new" model (pure semantics)
2. JS runtime wraps models in mutable wrappers
3. After `update`, reconcile: copy changed slots into old model
4. Old model reference preserved, slots mutated in-place

```javascript
function reconcile(oldModel, newModel) {
  const oldSlots = oldModel._slots;
  const newSlots = probeSlots(newModel);
  for (let i = 0; i < oldSlots.length; i++) {
    if (oldSlots[i] !== newSlots[i]) {
      oldSlots[i] = typeof newSlots[i] === 'function'
        ? wrapMutable(newSlots[i])
        : newSlots[i];
    }
  }
  return oldModel;  // same reference!
}
```

### Why Path A is sufficient (Agda sharing)

Path B (lenses with locate) was considered but **is not needed**. Here's why:

**Agda already does sharing:**
```javascript
// Agda update for "increment time" returns:
newModel = { time: oldModel.time + 1, audioBuffer: oldModel.audioBuffer }
//                                    ↑ SAME REFERENCE! Agda reuses it
```

**Reconcile leverages this:**
```javascript
for (let i = 0; i < slots.length; i++) {
  if (oldSlots[i] !== newSlots[i]) {  // reference comparison
    oldSlots[i] = newSlots[i];         // copy reference (not data!)
  }
  // unchanged slots: same reference → nothing to do
}
```

**Example with 100MB audio buffer:**
```
Model = { time: 0, audioBuffer: [100MB] }

dispatch(Tick):
  1. Agda update: { time: 1, audioBuffer: [same ref] }  // Agda sharing
  2. reconcile:
     - slots[0]: 0 !== 1 → copy value (4 bytes)
     - slots[1]: ref === ref → skip (100MB untouched!)
```

**Why Path B adds nothing:**
- Path B would bypass Agda `update` entirely
- But Agda `update` already avoids copying unchanged data
- Reconcile just "transfers" this sharing to mutable wrapper
- Extra complexity of Path B not justified

**Conclusion:** Path A + Agda sharing = optimal. No Path B needed.

### Step 3: Adapt `dispatch`

```javascript
function dispatch(msg) {
  if (cmdFunc) {
    const cmd = cmdFunc(msg)(model);
    executeCmd(cmd, dispatch);
  }

  // Agda update returns "new" model (pure)
  const newModel = update(msg)(model);

  // Reconcile: mutate old model in-place
  reconcile(model, newModel);

  // model reference unchanged, slots updated
  // updateScope uses reference comparison on slots
  updateScope(rootScope, model, model);
}
```

**Why this works:**
- `model` reference stays the same across dispatches
- Only changed `_slots[i]` get new references
- `changedSlotsFromCache` compares slot references — works correctly
- Bindings depending on unchanged slots are skipped

## What changes, what stays

| Component | Changes? | Details |
|-----------|----------|---------|
| `Lens.agda` | No | Stays pure (Path A) or adds `slotIdx` (Path B) |
| `Optic.agda` | No | Stays pure |
| `Node.agda` | No | Stays pure |
| Agda compiler output | No | Still emits Scott-encoded records |
| `dispatch()` | Yes | Wrap init, reconcile after update |
| `changedSlotsFromCache()` | No | Reference comparison still works! |
| `probeSlots()` | No | Used by reconcile and wrapMutable |
| `updateScope()` | No | Reference comparison on slots works |
| Binding update loop | No | Already uses `lastValue` cache |
| `createScope()` | No | `cachedArgs` still works |
| **NEW: `wrapMutable()`** | Add | Wraps Scott-encoded model for mutation |
| **NEW: `reconcile()`** | Add | Copies changed slots in-place |

## Tradeoffs

**Path A (runtime reconcile) — implemented:**
- Pro: Agda code unchanged, pure semantics preserved
- Pro: Minimal runtime changes (add wrapMutable, reconcile)
- Pro: Fallback trivial (just don't wrap)
- Pro: Leverages Agda's built-in sharing — large data not copied
- Con: `update` allocates temporary new model (but GC handles easily)
- Con: Reconcile is O(num_slots) per dispatch (but slots are few)

**Path B was considered but rejected:**
- Would bypass Agda `update` for "true O(1)" mutation
- But Agda already does sharing — unchanged slots reuse references
- Reconcile just transfers this sharing to mutable wrapper
- Extra complexity not justified for marginal gain

**Conclusion:** Path A is sufficient. Agda sharing + reconcile = optimal.

## Implementation details for Path A

### Core functions

**`probeCtor` — get constructor name:**
```javascript
function probeCtor(model) {
  if (typeof model !== 'function') return null;
  let ctor = null;
  try {
    model(new Proxy({}, {
      get(_, name) { return (...args) => { ctor = name; }; }
    }));
  } catch { return null; }
  return ctor;
}
```

**`wrapMutable` — make model slots accessible:**
```javascript
function wrapMutable(model) {
  if (model._slots) return model;  // already wrapped

  const args = probeSlots(model);
  const ctor = probeCtor(model);
  if (!args || !ctor) return model;

  // Recursively wrap nested structures
  const slots = args.map(a =>
    typeof a === 'function' ? wrapMutable(a) : a
  );

  // Wrapper closes over mutable slots array
  const wrapper = (cases) => cases[ctor](...slots);
  wrapper._slots = slots;
  wrapper._ctor = ctor;
  return wrapper;
}
```

**Key insight:** `wrapper._slots` IS the array used in the closure.
Mutating `_slots[i]` changes what `wrapper(cases)` returns!

**`reconcile` — copy changed slots in-place:**
```javascript
function reconcile(oldModel, newModel) {
  if (!oldModel._slots) return newModel;  // not wrapped

  const newArgs = probeSlots(newModel);
  if (!newArgs || newArgs.length !== oldModel._slots.length) {
    return newModel;  // structure changed, can't reconcile
  }

  // Copy changed slots in-place
  for (let i = 0; i < oldModel._slots.length; i++) {
    if (oldModel._slots[i] !== newArgs[i]) {
      oldModel._slots[i] = typeof newArgs[i] === 'function'
        ? wrapMutable(newArgs[i])
        : newArgs[i];
    }
  }

  return oldModel;  // same reference, mutated
}
```

### Updated `dispatch`

```javascript
function dispatch(msg) {
  if (cmdFunc) {
    const cmd = cmdFunc(msg)(model);
    executeCmd(cmd, dispatch);
  }

  const oldModel = model;
  const newModel = update(msg)(model);

  // Reconcile: copy changed slots into old model
  model = reconcile(model, newModel);

  // Reference comparison on _slots works correctly
  updateScope(rootScope, oldModel, model);
}
```

### Why existing `changedSlotsFromCache` still works

```javascript
function changedSlotsFromCache(scope, newModel) {
  const newArgs = probeSlots(newModel);  // reads from _slots
  // ...
  for (let i = 0; i < oldArgs.length; i++) {
    if (oldArgs[i] !== newArgs[i]) changed.add(i);  // reference comparison
  }
}
```

After reconcile:
- Unchanged slots: same reference → not in `changed` set
- Changed slots: new reference → in `changed` set
- Works perfectly with existing code!

### Edge cases

**1. Complete model replacement (different arity):**
```javascript
if (newArgs.length !== oldModel._slots.length) {
  return newModel;  // can't reconcile, use new model
}
```
Fall back to current behavior — replace model wholesale.

**2. First render (model not wrapped yet):**
```javascript
// In runReactiveApp initialization:
model = wrapMutable(init);
```
Wrap at startup, all subsequent updates work with mutable wrapper.

**3. Nested records:**
`wrapMutable` recursively wraps nested structures. When reconcile copies
a changed nested slot, it wraps the new value too.

**4. Lists (Scott-encoded cons cells):**
Lists are functions too — `wrapMutable` can wrap them. But for performance,
consider converting to JS arrays at model boundaries (existing `listToArray`).

### Testing checklist

1. [ ] Basic counter: dispatch increments, UI updates
2. [ ] Large array in model: change unrelated slot, verify array not copied
3. [ ] Nested records: change inner field, verify only that path updated
4. [ ] Model replacement: verify fallback to new model works
5. [ ] WebGL: verify buffer not re-uploaded when unrelated slot changes
6. [ ] Time-travel: verify history/replay works (uses structuredClone)
7. [ ] Hot reload: verify wrapped model survives template reload

## Affected files

- `runtime/reactive.js` — main target:
  - Add: `probeCtor()`, `wrapMutable()`, `reconcile()`
  - Modify: `runReactiveApp()` — wrap `init` model
  - Modify: `dispatch()` — call reconcile after update
  - Unchanged: `changedSlotsFromCache()`, `updateScope()`, `createScope()`
- No changes to any `.agda` file (Path A)
- No changes to `hs/` server code
- No changes to `runtime/events.js`

## Open questions

1. **Recursive wrapping depth:** `wrapMutable` recursively wraps all nested
   structures. For very deep models, this could be slow at init. Consider
   lazy wrapping (wrap on first access) if this becomes an issue.

2. **Lists in model:** Scott-encoded cons cells can be wrapped, but
   `listToArray` converts to JS Array on every render anyway. Consider:
   - Store as JS Array in model slots (mutable, O(1) index)
   - Convert at model boundary, not on every render
   - `foreachKeyed` already does key-based reconciliation

3. **BigLens serialization:** `JSON.stringify(model)` sees `_slots`, `_ctor`.
   Need custom serializer that extracts clean data:
   ```javascript
   function serializeModel(m) {
     if (!m._slots) return m;
     return m._slots.map(serializeModel);
   }
   ```

4. **Path B not needed:** Was considered for "true O(1)" mutation bypassing
   Agda `update`. But Agda sharing already ensures unchanged slots keep
   same references. Reconcile just transfers this — no extra optimization
   possible.

## Universality of the Ref-based approach

The mutable wrapper mechanism is **type-agnostic**. All data types work
uniformly through reference comparison:

```agda
-- All of these work identically:
wheelAngleLens : Lens Model Float         -- primitive
cameraPosLens  : Lens Model Vec3          -- small record
carModelLens   : Lens Model (Maybe LoadedModel)  -- large asset
verticesLens   : Lens Model (List Triangle)      -- huge array
texturesLens   : Lens Model (List TextureHandle) -- GPU resources
```

**The key insight:** changing one slot doesn't touch others.

```javascript
// Model with huge array in slot 5:
model._slots = [angle, pos, ..., hugeArray, ...]

// Update angle (slot 0):
model._slots[0] = newAngle;
// hugeArray reference unchanged — no copy!

// changedSlotsFromCache sees:
// slot 0: old !== new → changed
// slot 5: old === new → unchanged (same reference)
```

### Implications for WebGL and large data

1. **WebGL LoadedModel** — when only `wheelAngle` changes, `carModel` slot
   keeps same reference. `reactive-gl.js` compares references, skips
   re-uploading buffers.

2. **Large arrays** — same reference means same array. No copying, no
   re-upload, no re-render of dependent bindings.

3. **Nested structures** — recursively wrapped. Change propagates only
   along the modified path.

### Performance characteristics

| Operation | Complexity | Notes |
|-----------|------------|-------|
| `wrapMutable(model)` | O(n) | One-time at init, n = total slots |
| `reconcile(old, new)` | O(k) | k = top-level slots |
| Slot comparison | O(1) | Reference equality |
| Unchanged slot | O(0) | Not touched at all |

### Integration with WebGL Builder

```agda
record Model : Set where
  field
    wheelAngle  : Float           -- updated 60fps
    cameraAngle : Float           -- updated on drag
    carModel    : Maybe LoadedModel  -- large, rarely changes
    terrain     : List Triangle      -- huge, static
```

When `SpinWheels` fires 60 times per second:
- `reconcile` updates only `wheelAngle` slot
- `carModel` slot: same reference → `reactive-gl.js` skips buffer re-upload
- `terrain` slot: same reference → geometry stays in GPU memory

**Lenses unify the update mechanism across all data sizes.**

## Concurrency considerations

### Single-threaded (current)

JS is single-threaded. `dispatch` already has:
- `isUpdating` flag to detect re-entry
- `pendingMessages` queue for messages during update

Mutable wrappers work correctly — all mutations happen sequentially.

### Web Workers + SharedArrayBuffer (fast parallel processing)

For large data (audio, images, simulations) — use SharedArrayBuffer with
lenses for true parallel processing without serialization:

```javascript
// Main thread: create shared buffer
const audioBuffer = new SharedArrayBuffer(44100 * 4 * 60);  // 60 sec
const audioView = new Float32Array(audioBuffer);
model._slots[5] = audioView;

// Workers receive THE SAME buffer (zero-copy!)
worker1.postMessage({ buffer: audioBuffer, range: [0, 10000] });
worker2.postMessage({ buffer: audioBuffer, range: [10000, 20000] });
worker3.postMessage({ buffer: audioBuffer, range: [20000, 30000] });

// Each worker processes its range in parallel
// Main thread sees results immediately — no transfer needed
```

**Performance:**
- No serialization (buffer shared directly)
- No copying (workers write in-place)
- True parallelism (multiple cores)
- Results visible immediately

**Lenses for ranges:**
```agda
-- Lens focusing on array slice
sliceLens : ℕ → ℕ → Lens (Array A) (Slice A)

-- Worker 1: over (sliceLens 0 10000) process model
-- Worker 2: over (sliceLens 10000 20000) process model
-- Non-overlapping ranges — no conflicts
```

**BigLens modes:**
```
┌─────────────────────────────────────────────────────┐
│                    BigLens                          │
├─────────────────┬─────────────────┬─────────────────┤
│  Network mode   │  Shared mode    │  Transfer mode  │
│  (WebSocket)    │ (SharedArray)   │ (Transferable)  │
├─────────────────┼─────────────────┼─────────────────┤
│  Distributed    │  Local workers  │  One-way pass   │
│  Slow, reliable │  Fast, parallel │  Fast, one-shot │
└─────────────────┴─────────────────┴─────────────────┘
```

**⚠️ User responsibility for overlapping data:**

When multiple workers access overlapping ranges, the user must handle
synchronization explicitly:

```javascript
// SAFE: non-overlapping ranges (no sync needed)
worker1: range [0, 1000)
worker2: range [1000, 2000)

// UNSAFE: overlapping ranges (user must sync!)
worker1: range [0, 1500)
worker2: range [1000, 2000)  // overlap [1000, 1500)

// User options for overlapping access:
// 1. Atomics for individual elements
Atomics.store(view, i, value);
Atomics.load(view, i);

// 2. Atomics.wait/notify for coordination
Atomics.wait(syncArray, 0, 0);  // worker waits
Atomics.notify(syncArray, 0);    // main signals

// 3. Double-buffering (read from A, write to B, swap)

// 4. Redesign to avoid overlap
```

The runtime does NOT automatically synchronize SharedArrayBuffer access.
This is by design — automatic locking would kill performance. The user
chooses the appropriate strategy for their use case.

### BigLens (distributed/network optics)

Multiple clients updating same model via network:
```
Client A: over lens₁ f model  →  Server
Client B: over lens₂ g model  →  Server  // conflict?
```

**This requires versioning** — but for conflict resolution, not optimization:
- Optimistic: version per slot, reject stale updates
- CRDT: merge concurrent updates automatically
- OT: transform operations based on causal order

**Key insight:** local mutation doesn't need versions, distributed does.
These are separate concerns — local mutable wrapper + network versioning layer.

## Future: tagged arrays

### Current: Scott-encoded functions

Agda→JS compiles records as closures:
```javascript
{"_,_": c => c["_,_"](a, b)}
```

We wrap with `_slots` array for mutation.

### Future: tagged arrays

Potential future compiler output:
```javascript
["_,_", a, b]  // tag + slots
```

This is naturally mutable:
- `arr[0]` = constructor tag
- `arr[1], arr[2], ...` = slots
- Mutation: `arr[1] = newValue`

### Preparation: abstract slot access

To support both formats, abstract slot operations:

```javascript
// Check format
function isTaggedArray(model) {
  return Array.isArray(model) && typeof model[0] === 'string';
}

// Universal getters
function getSlots(model) {
  if (isTaggedArray(model)) return model.slice(1);
  if (model._slots) return model._slots;
  return probeSlots(model);  // fallback: probe function
}

function getCtor(model) {
  if (isTaggedArray(model)) return model[0];
  if (model._ctor) return model._ctor;
  return probeCtor(model);
}

// Universal setters
function setSlot(model, idx, value) {
  if (isTaggedArray(model)) {
    model[idx + 1] = value;  // +1 because arr[0] is tag
  } else if (model._slots) {
    model._slots[idx] = value;
  } else {
    throw new Error('Model not mutable — wrap first');
  }
}

// Universal wrapper
function ensureMutable(model) {
  if (isTaggedArray(model)) return model;  // already mutable
  if (model._slots) return model;           // already wrapped
  return wrapMutable(model);                // wrap function
}
```

### Migration path

1. **Now:** Use `wrapMutable` for Scott-encoded functions
2. **Later:** When compiler outputs tagged arrays, `ensureMutable` returns them as-is
3. **Code using `getSlots`/`setSlot`:** works unchanged

```javascript
// This code works for both formats:
function reconcile(oldModel, newModel) {
  const oldSlots = getSlots(oldModel);
  const newSlots = getSlots(newModel);

  for (let i = 0; i < oldSlots.length; i++) {
    if (oldSlots[i] !== newSlots[i]) {
      setSlot(oldModel, i, ensureMutable(newSlots[i]));
    }
  }
  return oldModel;
}
```

## Related documents

This implementation is the foundation for other optimizations:

### concurrency.md

Mutation reduces GC pressure and speeds up dispatch cycle. SharedArrayBuffer
in a slot works naturally — reconcile sees "same reference" and skips it.
This enables efficient worker-based parallel processing.

### shared-buffers.md

The "handle + version" pattern described there now works automatically:
- Put SharedArrayBuffer/ArrayBuffer in a model slot
- Reconcile compares by reference (O(1))
- Unchanged buffer = zero work
- Changed buffer = copy pointer only (8 bytes)

### Summary

```
┌─────────────────────────────────────────────────────────────┐
│                    Unified Architecture                      │
├─────────────────┬─────────────────┬─────────────────────────┤
│   mutation.md   │ concurrency.md  │   shared-buffers.md     │
│   (mechanism)   │ (performance)   │   (large data)          │
├─────────────────┼─────────────────┼─────────────────────────┤
│  wrapMutable    │  Less GC        │  SharedArrayBuffer      │
│  reconcile      │  Faster update  │  in slot = zero-copy    │
│  reference cmp  │  Worker-ready   │  Workers write directly │
└─────────────────┴─────────────────┴─────────────────────────┘
```

All three concerns are solved by one mechanism: **reference-based reconcile**.
