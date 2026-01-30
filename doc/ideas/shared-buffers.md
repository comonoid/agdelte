# Concurrent access to large shared state (blobs)

## Problem

Large binary data (images, audio buffers, video frames) cannot live inside
the Scott-encoded Agda model. They are too large to copy on every `update`,
and `postMessage` to a Worker copies via `structuredClone` -- 10MB per
message for a full HD image.

Lenses solve navigation and granular updates for structured data, but not
concurrent access to a flat byte buffer from multiple threads.

## The handle + version pattern

The Agda model stores only lightweight metadata. The actual blob lives
outside the model in a browser-managed buffer.

```
Model (Scott-encoded, pure, cheap)       Buffer (mutable, heavy, shared)
┌───────────────────────────┐            ┌──────────────────────────┐
│ imageVersion : ℕ          │            │ SharedArrayBuffer        │
│ brightness   : ℕ          │            │ (raw pixels / samples)   │
│ selection    : Rect       │            │                          │
│ chunkVersions : List ℕ    │            │                          │
└───────────────────────────┘            └──────────────────────────┘
        │                                         │
   Agda update                              Workers mutate
   (pure, fast, O(metadata))               (heavy, parallel)
```

Reactive bindings work on metadata. When `imageVersion` changes, a binding
triggers canvas redraw from the shared buffer. The buffer itself is never
part of the dispatch cycle.

## Two transfer strategies

### Strategy 1: Transferable ownership (move semantics)

`postMessage(buffer, [buffer])` transfers an `ArrayBuffer` to a Worker
without copying. The sender loses access -- exactly like Rust's move.

```javascript
// Main thread → Worker: transfer ownership
worker.postMessage({ pixels: buffer }, [buffer]);
// buffer.byteLength === 0 here -- ownership moved

// Worker → Main thread: transfer back
self.postMessage({ pixels: processed }, [processed]);
```

For parallelism, split into chunks (like Rust `chunks_mut`):

```
Image 1920x1080, 4 bytes/pixel = ~8MB
  chunk0: ArrayBuffer (270 rows) → Worker 0
  chunk1: ArrayBuffer (270 rows) → Worker 1
  chunk2: ArrayBuffer (270 rows) → Worker 2
  chunk3: ArrayBuffer (270 rows) → Worker 3
```

Each worker has exclusive ownership of its chunk. No synchronization needed.
Main thread reassembles after all workers return.

Pros:
- No shared memory, no synchronization, no `Atomics`
- Works in all browsers (no COOP/COEP headers needed)
- Clean ownership model, easy to reason about

Cons:
- Overhead of splitting and reassembling
- Main thread cannot read buffer while worker holds it
- If processing needs neighbor data (blur, convolution), chunks need
  halo/ghost regions -- overlapping borders copied redundantly
- Ping-pong latency: main → worker → main for each operation

### Strategy 2: SharedArrayBuffer (shared memory)

All threads see the same memory. No copying, no transfer.

```javascript
// Setup (once)
const sab = new SharedArrayBuffer(1920 * 1080 * 4);
const pixels = new Uint8Array(sab);

// Main thread and all workers share `sab`
worker0.postMessage({ buffer: sab, startRow: 0,   endRow: 270 });
worker1.postMessage({ buffer: sab, startRow: 270, endRow: 540 });
worker2.postMessage({ buffer: sab, startRow: 540, endRow: 810 });
worker3.postMessage({ buffer: sab, startRow: 810, endRow: 1080 });
```

Synchronization options:

1. **Convention-based** -- each worker writes only to its assigned region.
   No overlap, no locks. Like Rust unsafe with manual non-aliasing guarantee.

2. **Atomics** -- `Atomics.wait()` / `Atomics.notify()` for coordination.
   Worker signals completion, main thread waits for all workers before
   reading.

3. **Version flags** -- each chunk has an atomic version counter in a
   separate `SharedArrayBuffer` (or first N bytes of the main one).
   Workers bump version after writing. Main thread polls or waits.

```javascript
// Coordination buffer: one Int32 per chunk
const coord = new SharedArrayBuffer(4 * NUM_CHUNKS);
const versions = new Int32Array(coord);

// Worker k, after processing:
Atomics.store(versions, k, Atomics.load(versions, k) + 1);
Atomics.notify(versions, k);

// Main thread, waiting for chunk k:
Atomics.wait(versions, k, currentVersion);
// chunk k is ready, redraw
```

Pros:
- Zero-copy -- true shared memory
- Workers can read neighbor data for convolution/blur without halo regions
- No reassembly step
- Main thread can read buffer at any time (for display)

Cons:
- Requires COOP/COEP HTTP headers on the server:
  `Cross-Origin-Opener-Policy: same-origin`
  `Cross-Origin-Embedder-Policy: require-corp`
- More complex synchronization
- Potential for data races if conventions are violated
- Not available in all contexts (e.g. some iframes, cross-origin)

### Strategy 3: OffscreenCanvas (for images specifically)

For image/canvas workloads, `OffscreenCanvas` can be transferred to a worker:

```javascript
const offscreen = canvas.transferControlToOffscreen();
worker.postMessage({ canvas: offscreen }, [offscreen]);

// Worker draws directly -- result visible on main thread's canvas
// No buffer copying, no readback needed for display
```

Pros:
- Purpose-built for image rendering
- No buffer management, browser handles display
- WebGL available in worker

Cons:
- Only for canvas output (not general blob processing)
- Once transferred, main thread cannot draw on that canvas
- Not suitable for audio or non-visual data

## Integration with Agdelte

### Model layer (Agda)

```agda
record ImageMeta : Set where
  field
    version      : ℕ           -- bumped when buffer content changes
    width height : ℕ
    selection    : Maybe Rect
    brightness   : ℕ            -- UI-controlled parameter

-- Lens into image metadata within larger model
imageLens : Lens Model ImageMeta
```

The model never contains pixel data. `update` modifies only metadata.
This is cheap and stays in the pure Agda dispatch cycle.

### Runtime layer (reactive.js)

```javascript
// Buffer registry -- lives outside the model
const buffers = new Map();  // handle -> SharedArrayBuffer | ArrayBuffer

function registerBuffer(handle, sab) {
  buffers.set(handle, sab);
}

// Binding for canvas: extract version from model, redraw if changed
// This is a regular binding -- no special runtime support needed
// The extract function returns the version string
// When version changes, the binding callback redraws from buffer
```

### Worker coordination

```javascript
// In dispatch, after model update:
const oldVersion = oldMeta.version;
const newVersion = newMeta.version;

if (oldVersion !== newVersion) {
  // Metadata changed -- maybe brightness slider moved
  // Send new parameters to worker pool
  workerPool.process({
    buffer: buffers.get('main-image'),
    brightness: newMeta.brightness,
    region: { start: 0, end: height }
  });
  // Worker modifies buffer in-place (SharedArrayBuffer)
  // or returns processed buffer (Transferable)
  // On completion: bump model version, trigger canvas rebind
}
```

### Canvas binding

A new binding type or FFI hook for canvas rendering:

```javascript
// In renderNode, handle a canvas bind:
canvasBind: (meta, drawFn) => {
  const canvas = document.createElement('canvas');
  canvas.width = meta.width;
  canvas.height = meta.height;
  const ctx = canvas.getContext('2d');

  // Register as a binding that redraws when version changes
  currentScope.bindings.push({
    node: canvas,
    binding: versionBinding,
    lastValue: null,
    update: () => {
      const buf = buffers.get(meta.handle);
      const imageData = new ImageData(
        new Uint8ClampedArray(buf),
        meta.width, meta.height
      );
      ctx.putImageData(imageData, 0, 0);
    }
  });
  return canvas;
}
```

## Relation to other ideas

### mutation.md

In-place mutation of the Agda model is about avoiding copies of the
Scott-encoded structure. Shared buffers are about avoiding copies of raw
binary data. They are complementary:
- Model mutation: O(1) update of metadata fields
- Shared buffers: O(0) transfer of blob data (zero-copy)

### concurrency.md

Batching and rAF sync apply to blob updates too. Multiple parameter changes
(brightness + contrast + crop) within one frame should produce one worker
dispatch, not three. The priority system should treat worker completion
callbacks as P2 (not urgent -- next frame is fine for canvas redraw).

## Preferred architecture for Agdelte

The most natural fit for Agdelte is **one SharedArrayBuffer + convention-based
regions + version tracking in the model**. Zero-copy everywhere:

```
SharedArrayBuffer (8MB, e.g. 1920x1080x4)
┌────────────┬────────────┬────────────┬────────────┐
│  chunk 0   │  chunk 1   │  chunk 2   │  chunk 3   │
│  Worker 0  │  Worker 1  │  Worker 2  │  Worker 3  │
│ rows 0-269 │rows 270-539│rows 540-809│rows 810-1079│
└────────────┴────────────┴────────────┴────────────┘
        ↑ all workers write to their region only
        ↑ main thread reads freely for canvas display

Model (Agda, pure):
  record ImageModel : Set where
    field
      chunkVersions : Vec 4 ℕ    -- per-chunk version counter
      brightness    : ℕ
      selection     : Maybe Rect
```

Flow:

1. User changes brightness → `dispatch` → `update` bumps `brightness` in
   model (pure, O(1))
2. Runtime sees `brightness` changed → sends new parameters to all 4 workers
   (each gets `{buffer: sab, startRow, endRow, brightness}`)
3. Each worker processes its chunk in-place in the SharedArrayBuffer
4. Each worker bumps its version via `Atomics.store`
5. Main thread binding on `chunkVersions` detects change →
   `ctx.putImageData(...)` redraws canvas from the same SharedArrayBuffer

**No data is copied at any point.** Workers write directly into shared memory.
Main thread reads directly from shared memory for display. The Agda model
tracks only versions and parameters -- lightweight values that flow through
the normal lens/binding pipeline.

This is the zero-copy ideal: the dispatch cycle handles metadata (fast, pure,
type-checked), while heavy data lives in shared memory managed by the runtime.

## Recommendation

1. Start with **handle + version** pattern -- model stores metadata only,
   buffer is a plain `ArrayBuffer` in a registry. No workers yet, just
   separation of concerns.

2. Add **Transferable** ping-pong for single-worker processing (e.g. apply
   filter). Simple, no COOP/COEP headers.

3. Move to **SharedArrayBuffer** when parallel processing is needed (multiple
   workers on chunks). Requires server headers.

4. **OffscreenCanvas** as optimization for display-only paths.

## Server requirements for SharedArrayBuffer

The Haskell server (`hs/Agdelte/AgentServer.hs`) must send these headers:

```
Cross-Origin-Opener-Policy: same-origin
Cross-Origin-Embedder-Policy: require-corp
```

This is a two-line change in `Http.hs` response construction.

## Open questions

1. How to express buffer handles in Agda types? Opaque postulate
   (`postulate BufferHandle : Set`) or a typed wrapper with dimensions?
2. Should the buffer registry be global or per-app?
3. How to handle buffer lifecycle (allocation, deallocation)? Reference
   counting via model presence, or explicit `Cmd` for alloc/free?
4. For audio: `AudioWorklet` is a separate API from Web Workers. Need a
   unified abstraction or separate handling?
5. How does this interact with BigLens (network optics)? Server cannot peek
   into a SharedArrayBuffer. Probably: server peeks metadata only, blob
   stays client-side.
