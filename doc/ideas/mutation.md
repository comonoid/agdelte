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

## Proposed design: version-stamped mutation

### Core idea

Instead of comparing slot references (which are identity-based), track a
**version counter per slot path**. When a lens does `set`, it bumps the
version of the affected path. The scope optimisation checks versions instead
of reference equality.

### Step 1: Mutable model wrapper

Wrap the model in a thin layer that tracks mutations:

```javascript
function createMutableModel(initial) {
  return {
    value: initial,       // the actual model (Scott-encoded)
    version: 0,           // global version, bumped on every update
    slotVersions: null,   // per-slot versions, lazily initialized
  };
}
```

### Step 2: Lens-aware `set` at runtime level

The key change: instead of letting Agda's compiled `update` create a new
model, intercept at the `dispatch` level. Two strategies:

**Strategy A -- post-hoc (simpler, less optimal):**
Keep `update` as-is (it returns a new model). But after `update`, do NOT
replace `model` wholesale. Instead, diff the old and new at the top-level
slot level, mutate the old model's slots in-place for unchanged parts, and
bump versions only for changed slots.

This doesn't save the allocation inside `update`, but it makes `updateScope`
cheaper because unchanged sub-trees keep their identity.

**Strategy B -- intercepting `set` (optimal, more complex):**
Provide a JS-level `set` implementation for lenses that mutates the
Scott-encoded record in-place. A Scott-encoded record like:

```javascript
// Agda record {x = 3, y = "hello"} compiles to:
const model = (cases) => cases["mkRecord"](3, "hello");
```

To mutate slot 0 in-place, we need the record to close over a mutable array:

```javascript
function mutableRecord(ctor, args) {
  const slots = [...args];  // mutable array
  const self = (cases) => cases[ctor](...slots);
  self._slots = slots;      // escape hatch for mutation
  self._ctor = ctor;
  self._version = 0;
  self._slotVersions = new Array(slots.length).fill(0);
  return self;
}
```

Then a lens `set` at the JS level:

```javascript
function lensSetMut(lensPath, value, model) {
  // lensPath = [0] means "slot 0 of top-level record"
  // lensPath = [1, 2] means "slot 2 of slot 1"
  let target = model;
  for (let i = 0; i < lensPath.length - 1; i++) {
    target = target._slots[lensPath[i]];
  }
  const lastIdx = lensPath[lensPath.length - 1];
  target._slots[lastIdx] = value;
  // Bump versions along the path
  model._version++;
  // ... bump intermediate versions as needed
}
```

### Step 3: Adapt `changedSlotsFromCache`

Replace reference comparison with version comparison:

```javascript
function changedSlotsFromCache(scope, newModel) {
  if (!newModel._slotVersions) return null; // fallback
  const newVersions = newModel._slotVersions;
  const oldVersions = scope.cachedSlotVersions;
  scope.cachedSlotVersions = [...newVersions];
  if (!oldVersions) return null;
  const changed = new Set();
  for (let i = 0; i < newVersions.length; i++) {
    if (oldVersions[i] !== newVersions[i]) changed.add(i);
  }
  return changed;
}
```

### Step 4: Adapt `dispatch`

```javascript
function dispatch(msg) {
  const oldVersion = model._version;

  if (cmdFunc) {
    const cmd = cmdFunc(msg)(model);
    executeCmd(cmd, dispatch);
  }

  // Strategy A: let update run, then reconcile
  const newModel = update(msg)(model);
  reconcileMutation(model, newModel);  // mutate model in-place, bump versions
  // model is now updated in-place

  updateScope(rootScope);  // no oldModel needed; uses versions
}
```

## What changes, what stays

| Component | Changes? | Details |
|-----------|----------|---------|
| `Lens.agda` | No | Stays pure |
| `Optic.agda` | No | Stays pure |
| `Node.agda` | No | Stays pure |
| Agda compiler output | No | Still emits Scott-encoded records |
| `dispatch()` | Yes | Reconcile or intercept mutation |
| `changedSlotsFromCache()` | Yes | Version-based instead of reference-based |
| `probeSlots()` | Maybe | Could be replaced by `_slotVersions` |
| `updateScope()` | Minor | Remove `oldModel` parameter if using versions |
| Binding update loop | No | Already uses `lastValue` cache |
| `createScope()` | Minor | Store `cachedSlotVersions` instead of `cachedArgs` |

## Tradeoffs

**Strategy A (post-hoc reconcile):**
- Pro: Agda output untouched, minimal changes in runtime
- Pro: Fallback to current behavior trivial (just skip reconcile)
- Con: `update` still allocates a new model; savings only in scope skipping
- Con: Top-level reconcile is O(num_slots), not O(1)

**Strategy B (mutable records):**
- Pro: True O(1) mutation, no allocation for unchanged parts
- Pro: Version tracking is precise and cheap
- Con: Requires changing the JS representation of Scott-encoded records
- Con: All record construction must go through `mutableRecord`
- Con: Agda's compiled `_,_` and record constructors need wrapping

**Recommendation:** Start with Strategy A. It requires changes only in
`reactive.js` (no compiler changes) and already solves the main problem: scope
skipping works correctly with large models. Strategy B is a follow-up
optimisation if allocation pressure from `update` becomes measurable.

## Affected files

- `runtime/reactive.js` -- main target: `dispatch`, `changedSlotsFromCache`,
  `probeSlots`, `updateScope`, `createScope`
- No changes to any `.agda` file
- No changes to `hs/` server code
- No changes to `runtime/events.js` or `runtime/dom.js`

## Open questions

1. **Nested records:** Strategy A reconciles only top-level slots. For deeply
   nested models, intermediate records also get copied. Is one level enough?
   Probably yes if `scopeProj` + `zoomNode` already partition the model into
   small sub-trees.

2. **Lists in model:** Agda lists compile to Scott-encoded cons cells (the
   backend translates all inductive types uniformly, no special case for
   `List`). But `runtime/reactive.js:listToArray` already converts them to
   JS arrays on every render. A natural optimisation: convert to `Array`
   once at model initialisation and mutate in-place. This is a runtime-level
   decision, independent of the Agda compiler. `foreachKeyed` already does
   key-based reconciliation, so list mutation fits naturally.

3. **`scope.fingerprint`:** String fingerprints still work under mutation
   (they re-extract). No changes needed.

4. **Interaction with BigLens (network optics):** `wsPeekClient` serializes
   the model with `JSON.stringify`. Mutable records with `_slots` would need
   a custom serializer. Strategy A avoids this since the model shape is
   unchanged.
