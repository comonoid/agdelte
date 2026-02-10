# Agdelte TODO

Future improvements and features.

## Runtime Performance

### Priority Scheduling

**Why:** Not all messages are equal. Keyboard input needs immediate response,
while background data fetches can wait. Currently all messages go through
the same batched queue.

**Goal:** Keyboard/focus events process instantly (P0), clicks batch per frame
(P1), data fetches run in idle time (P2).

### Time-Slicing updateScope

**Why:** For huge DOM trees (1000+ bindings), `updateScope` can take >16ms,
blocking the main thread and causing jank.

**Goal:** Break DOM updates into chunks, yield to browser between chunks,
maintain 60fps even with massive UIs.

### Web Worker for update

**Why:** Heavy `update` computations (sorting 100k rows, complex calculations)
block the main thread. The pure Agda `update` function could run in a worker.

**Goal:** Offload `update` to worker, keep main thread responsive. Challenges:
Scott-encoded closures aren't serializable — need tagged arrays or worker
with its own Agda module copy.

## Large Data Handling

### Buffer Registry

**Why:** Canvas/WebGL apps need to reference large buffers (images, audio)
without passing them through the Agda model on every render.

**Goal:** Registry mapping handles to SharedArrayBuffer. Model stores only
lightweight metadata (version, dimensions), buffer lives in registry.

### Server Headers for SharedArrayBuffer

**Why:** SharedArrayBuffer requires specific HTTP headers to work in browsers
(security restriction after Spectre).

**Goal:** Add COOP/COEP headers to Haskell server:
```
Cross-Origin-Opener-Policy: same-origin
Cross-Origin-Embedder-Policy: require-corp
```

## WebGL

### Pick Buffer Improvements

**Why:** Current pick buffer assigns one ID per mesh. For composite objects
(button = frame + background + text), clicking any part should trigger
the group's event.

**Goal:** Groups get single pick ID. Named parts get sub-IDs. Instanced
geometry encodes instance index in pick color.

### Geometry Batching

**Why:** Each `mesh` = separate draw call. 100 buttons = 300+ draw calls.
Static geometry with same material could be combined.

**Goal:** `batch` combinator merges vertex buffers, single draw call.

### Instancing

**Why:** Many copies of same geometry (trees, particles) currently each
require separate draw call.

**Goal:** WebGL2 instancing support. Per-instance transform/color attributes.
Interactive instancing returns instance index on click.

## See Also

- `doc/ideas/webgl-builder.md` — comprehensive WebGL builder library design
- `doc/ideas/webgl-controls.md` — 3D UI controls (buttons, sliders, etc.)
