# Browser-side concurrency for Agdelte runtime

## Current state

The runtime (`runtime/reactive.js`) is essentially single-threaded and
synchronous. The dispatch cycle is:

```javascript
function dispatch(msg) {
  if (isUpdating) {
    pendingMessages.push(msg);  // queue if busy
    return;
  }
  isUpdating = true;
  const oldModel = model;
  model = update(msg)(oldModel);          // synchronous, blocks main thread
  updateScope(rootScope, oldModel, model); // synchronous DOM updates
  // process queued messages one by one
  while (pendingMessages.length > 0) { ... }
  isUpdating = false;
}
```

What exists:
- `pendingMessages` queue -- messages arriving during update are deferred
- `executeCmd` -- side-effects (HTTP, timers) run asynchronously
- WebSocket exchange with server (BigLens peek/over protocol)

What is missing:
- No way to offload heavy `update` to a background thread -- UI blocks
- No batching -- 10 messages in a row = 10 separate `updateScope` passes
- No priorities -- scroll event and button click treated identically
- No cancellation -- a started update cannot be preempted
- No `requestAnimationFrame` sync -- DOM updated immediately in dispatch,
  even if the browser is not ready to paint

## Problem

For simple apps (counters, forms, small lists) this is fine. For complex UIs
(grids, trees, real-time data, animations) the main thread can be blocked by:

1. **Heavy `update`** -- sorting 100k rows, processing large data structures
2. **Heavy `updateScope`** -- thousands of bindings to check, deep scope trees
3. **Message storms** -- scroll/mousemove/resize generating dozens of events
   per frame, each triggering a full dispatch cycle

## Proposed improvements

### 1. Batching

Collect all messages within a single microtask or rAF frame and apply them
as one batch:

```javascript
let batchQueue = [];
let batchScheduled = false;

function dispatch(msg) {
  batchQueue.push(msg);
  if (!batchScheduled) {
    batchScheduled = true;
    requestAnimationFrame(flushBatch);
  }
}

function flushBatch() {
  batchScheduled = false;
  const msgs = batchQueue;
  batchQueue = [];
  const oldModel = model;
  for (const msg of msgs) {
    model = update(msg)(model);
  }
  updateScope(rootScope, oldModel, model);  // ONE scope update for all messages
}
```

Benefits:
- 10 scroll events per frame -> 1 updateScope pass
- Naturally synced with browser paint cycle via rAF

Trade-off:
- Adds up to 16ms latency to every message (one frame)
- Some messages (keyboard input) may want synchronous dispatch
- Need a way to mark messages as "immediate" vs "batchable"

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

### Mutation (doc/ideas/mutation.md)

In-place mutation reduces allocation pressure, which helps all concurrency
strategies (less GC pause, faster `update`). But mutation + Worker is tricky:
can't share mutable model across threads. Worker strategy likely needs
immutable model (or `SharedArrayBuffer` for flat data like images).

### Virtual scroll (future)

Batching + rAF sync is almost mandatory for virtual scroll. Without it,
scroll events trigger dozens of dispatch cycles per second.

## Recommendation

Start with **batching** (#1) -- simplest, biggest impact. Then add **priority
dispatch** (#2) for input responsiveness. Time-slicing (#3) and Worker (#4)
are more complex and only needed for genuinely heavy workloads.

## Affected files

- `runtime/reactive.js` -- `dispatch`, `updateScope`, new scheduler logic
- `runtime/events.js` -- subscription events may need priority tagging
- No changes to Agda source
- No changes to Haskell server

## Open questions

1. Should batching be opt-in (per app) or default behavior?
2. How to mark message priority -- at the Agda level (`Msg` metadata) or
   runtime level (event type heuristic)?
3. Is `SharedArrayBuffer` viable for sharing large blobs (images, audio)
   between main thread and worker without copying?
4. How does time-slicing interact with CSS transitions/animations triggered
   by binding updates?
