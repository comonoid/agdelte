# Browser-side concurrency for Agdelte runtime

## Current state — UPDATED

The runtime (`runtime/reactive.js`) now has **batching** and **in-place mutation**
implemented. The dispatch cycle is:

```javascript
// Batched dispatch (default) — collects messages, applies in rAF
function dispatch(msg) {
  batchQueue.push(msg);
  if (!batchScheduled) {
    batchScheduled = true;
    requestAnimationFrame(flushBatch);
  }
}

// Immediate dispatch — for keyboard input, focus events
function dispatchSync(msg) { ... }

function flushBatch() {
  for (const msg of msgs) {
    model = reconcile(model, update(msg)(model));  // in-place mutation
  }
  updateScope(rootScope, oldModel, model);  // ONE pass for all messages
}
```

What exists now:
- **Batching** — multiple messages per frame → one `updateScope` pass
- **rAF sync** — DOM updates aligned with browser paint cycle
- **In-place mutation** — `reconcile` reuses model slots, reduces GC pressure
- **Immediate dispatch** — `dispatchSync` for keyboard/focus (bypasses batching)
- `executeCmd` — side-effects (HTTP, timers) run asynchronously
- WebSocket exchange with server (BigLens peek/over protocol)

What is still missing:
- No way to offload heavy `update` to a background thread — UI blocks
- No priorities — scroll event and button click treated identically (both batched)
- No cancellation — a started update cannot be preempted
- No time-slicing — large `updateScope` still blocks until complete

## Problem

For simple apps (counters, forms, small lists) this is fine. For complex UIs
(grids, trees, real-time data, animations) the main thread can be blocked by:

1. **Heavy `update`** -- sorting 100k rows, processing large data structures
2. **Heavy `updateScope`** -- thousands of bindings to check, deep scope trees
3. **Message storms** -- scroll/mousemove/resize generating dozens of events
   per frame, each triggering a full dispatch cycle

## Proposed improvements

### 1. Batching — IMPLEMENTED

**Status:** Implemented in `runtime/reactive.js`.

```javascript
// dispatch(msg) — batched, waits for rAF
// dispatchSync(msg) — immediate, no batching

function dispatch(msg) {
  batchQueue.push(msg);
  if (!batchScheduled) {
    batchScheduled = true;
    requestAnimationFrame(flushBatch);
  }
}

function flushBatch() {
  // Apply all messages, then ONE updateScope
  for (const msg of msgs) {
    model = reconcile(model, update(msg)(model));
  }
  updateScope(rootScope, oldModel, model);
}
```

**Benefits:**
- 10 scroll events per frame → 1 updateScope pass
- Naturally synced with browser paint cycle via rAF
- `dispatchSync` available for immediate response (keyboard, focus)

**API:**
- `dispatch(msg)` — batched (default, use for most events)
- `dispatchSync(msg)` — immediate (use for keyboard input)

### 2. Priority scheduling

Not all messages are equal. User interactions should preempt data fetches.
A simple priority scheme:

```
P0 (sync):      keyboard input, focus events    -- dispatch immediately
P1 (next frame): clicks, form changes            -- next rAF
P2 (idle):       data fetches, background updates -- requestIdleCallback
P3 (low):        analytics, prefetching           -- when nothing else to do
```

Implementation: separate queues per priority level, `flushBatch` drains P0
first, then P1, etc. If time budget (e.g. 8ms) is exceeded, defer remaining
to next frame.

This is conceptually similar to React's Scheduler (`scheduler` package) but
much simpler because Agdelte's update model is already pure (Msg -> Model ->
Model) -- no hooks, no effects during render.

### 3. Time-slicing updateScope

For large scope trees, `updateScope` can take >16ms. Break it into chunks:

```javascript
async function updateScopeSliced(scope, oldModel, newModel) {
  const queue = [scope];
  const deadline = performance.now() + 8; // 8ms budget

  while (queue.length > 0) {
    const s = queue.shift();
    updateScopeShallow(s, oldModel, newModel); // only this scope, not children
    queue.push(...s.children);

    if (performance.now() > deadline) {
      await nextFrame();  // yield to browser
      deadline = performance.now() + 8;
    }
  }
}
```

Trade-off:
- Partially updated DOM is visible between slices (tearing)
- May need double-buffering or deferred DOM application
- Complexity increases significantly

### 4. Web Worker for `update`

Offload the pure `update` function to a Worker:

```
Main thread                    Worker
-----------                    ------
dispatch(msg)
  -> postMessage({msg, model})
                               model = update(msg)(model)
                               postMessage({newModel})
  <- onmessage
  updateScope(root, old, new)
```

Benefits:
- `update` cannot block main thread
- Main thread stays responsive during heavy computation

Challenges:
- Model must be serializable (`structuredClone` / `postMessage`)
- Scott-encoded closures are NOT serializable -- need a serialization layer
  or the worker must have its own copy of the compiled Agda module
- Round-trip overhead via `postMessage` adds latency
- Need to handle messages arriving while worker is busy (queue on main
  thread, send latest model when worker is free)

Possible approach: worker loads the same compiled Agda JS module. Main thread
sends only the message (small). Worker maintains its own model copy, runs
`update`, sends back the new model serialized (or just a diff/patch).

### 5. Concurrent list/tree rendering

For virtual scroll (future `virtualForeach`):
- Render visible items synchronously (critical path)
- Render off-screen buffer items via `requestIdleCallback`
- On scroll, swap pre-rendered items in, start rendering next buffer

This is independent of the other strategies and specific to large
collections.

### 6. Cancellation

If a new message arrives while a sliced `updateScope` is in progress:
- Option A: finish current slice, then apply new message on top
- Option B: abort current update, restart with merged state
- Option C: priority-based -- only higher priority cancels lower

For Worker-based `update`:
- If worker is processing msg1 and msg2 arrives, queue msg2
- When worker returns, apply both: `update(msg2)(update(msg1)(old))`
- Or: send msg2 to worker, let it chain

## Interaction with other ideas

### Mutation (doc/ideas/mutation.md) — IMPLEMENTED

**Status:** In-place mutation via `wrapMutable` + `reconcile` is now implemented
in `runtime/reactive.js`.

**How it helps concurrency:**

1. **Less GC pressure** — reconcile reuses model reference, only changed slots
   get new values. Fewer allocations = fewer GC pauses.

2. **Faster dispatch cycle** — Agda `update` still creates temporary model, but
   reconcile is O(k) reference comparisons (k = number of slots). Very fast.

3. **SharedArrayBuffer works naturally** — if a slot contains SharedArrayBuffer,
   reconcile sees "same reference" and skips it entirely:
   ```javascript
   // Model: { brightness: 50, audioBuffer: SharedArrayBuffer(100MB) }
   // dispatch(ChangeBrightness 60):
   //   reconcile: slots[0] changed (50 → 60), copy value
   //   reconcile: slots[1] === slots[1] → SKIP (100MB untouched!)
   ```

4. **Worker-compatible** — mutable wrapper stays on main thread. Workers receive
   SharedArrayBuffer reference (same memory). No conflict.

**Conclusion:** Mutation implementation is the foundation for all concurrency
optimizations. Batching (#1) and priority scheduling (#2) build on top of it.

### Virtual scroll (future)

Batching + rAF sync is almost mandatory for virtual scroll. Without it,
scroll events trigger dozens of dispatch cycles per second.

## Recommendation

~~Start with **batching** (#1) -- simplest, biggest impact.~~ **DONE.**

Next: add **priority dispatch** (#2) for input responsiveness. Time-slicing (#3)
and Worker (#4) are more complex and only needed for genuinely heavy workloads.

## Affected files

- `runtime/reactive.js` -- `dispatch`, `updateScope`, new scheduler logic
- `runtime/events.js` -- subscription events may need priority tagging
- No changes to Agda source
- No changes to Haskell server

## Open questions

1. ~~Should batching be opt-in (per app) or default behavior?~~
   **RESOLVED:** Batching is default. `dispatchSync` available for immediate.

2. How to mark message priority — at the Agda level (`Msg` metadata) or
   runtime level (event type heuristic)?

3. ~~Is `SharedArrayBuffer` viable for sharing large blobs (images, audio)
   between main thread and worker without copying?~~
   **RESOLVED:** Yes. See `shared-buffers.md`. Reconcile skips unchanged refs.

4. How does time-slicing interact with CSS transitions/animations triggered
   by binding updates?
