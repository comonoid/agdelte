/**
 * Agdelte Reactive Runtime
 * Renders ReactiveApp with direct DOM updates (no Virtual DOM)
 * Like Svelte - bindings track which DOM nodes need updating
 *
 * Error Handling Pattern:
 * - console.error: Fatal errors (module load failed, invariant violations)
 * - console.warn: Recoverable issues (element not found, fallback used, depth exceeded)
 * - Silent: Expected edge cases (empty cmd, missing optional features)
 */

import { interpretEvent, unsubscribe, wsConnections, channelConnections } from './events.js';
import { deepEqual, countSlots, detectSlots, probeSlots, probeCtor, changedSlotsFromCache, listToArray, ensureNumber } from './agda-values.js';
import { bufferRegistry, mkBufferHandle, extractBufferHandle } from './buffer-registry.js';

// ─────────────────────────────────────────────────────────────────────
// SVG/MathML namespace support
// ─────────────────────────────────────────────────────────────────────

const SVG_NS = 'http://www.w3.org/2000/svg';
const MATHML_NS = 'http://www.w3.org/1998/Math/MathML';

// SMIL animation elements that need manual start when dynamically created
const SMIL_TAGS = ['animate', 'animateTransform', 'animateMotion', 'set'];

/**
 * Start SMIL animations that don't auto-start when dynamically created.
 * Handles:
 * - Numeric begin values: "0s", "1s", "100ms", "0.5s"
 * - Syncbase refs: "anim1.end", "anim1.begin+1s" (starts the referenced anim first)
 * Does NOT auto-start:
 * - Event-based: "click", "mouseover" (browser handles these)
 * - "indefinite" (requires explicit beginElement() call)
 */
function startSmilAnimations(container) {
  // Use requestAnimationFrame to ensure DOM is fully painted
  requestAnimationFrame(() => {
    // First pass: collect all animations and their dependencies
    const allAnims = [];
    const animById = new Map();

    for (const tag of SMIL_TAGS) {
      for (const anim of container.getElementsByTagName(tag)) {
        allAnims.push(anim);
        const id = anim.getAttribute('id');
        if (id) animById.set(id, anim);
      }
    }

    // Track which animations we've started
    const started = new Set();

    function startAnim(anim) {
      if (started.has(anim)) return;
      started.add(anim);

      const begin = anim.getAttribute('begin') || '0s';

      // Check for syncbase reference (e.g., "anim1.end", "anim1.begin+1s")
      const syncMatch = begin.match(/^([a-zA-Z_][\w-]*)\.(?:begin|end)/);
      if (syncMatch) {
        const refId = syncMatch[1];
        const refAnim = animById.get(refId);
        if (refAnim) startAnim(refAnim); // Start dependency first
      }

      // Start if numeric begin (0, 0s, 0.5s, 100ms, etc.)
      if (/^[\d.]/.test(begin)) {
        if (typeof anim.beginElement === 'function') {
          try { anim.beginElement(); } catch (e) { /* ignore */ }
        }
      }
    }

    // Start all animations
    for (const anim of allAnims) {
      startAnim(anim);
    }
  });
}

// HTML boolean attributes — presence means true, absence means false
const BOOL_ATTRS = new Set([
  'disabled', 'checked', 'readonly', 'required', 'selected',
  'hidden', 'autofocus', 'multiple', 'open', 'novalidate',
  'formnovalidate', 'autoplay', 'controls', 'loop', 'muted',
  'default', 'reversed', 'allowfullscreen', 'async', 'defer',
]);

// Namespaced attributes (xlink:href, xml:lang, etc.)
const ATTR_NS = {
  'xlink:href': 'http://www.w3.org/1999/xlink',
  'xlink:title': 'http://www.w3.org/1999/xlink',
  'xml:lang': 'http://www.w3.org/XML/1998/namespace',
  'xml:space': 'http://www.w3.org/XML/1998/namespace',
};

/**
 * Detect Content-Type for HTTP POST body.
 * Returns 'application/json' if body looks like valid JSON, otherwise 'text/plain'.
 */
function detectContentType(body) {
  if (typeof body === 'string' && body.length > 0) {
    const ch = body[0];
    if (ch === '{' || ch === '[' || ch === '"') {
      try { JSON.parse(body); return 'application/json'; } catch {}
    }
  }
  return 'text/plain';
}

/**
 * Execute a Task (monadic chain of async operations).
 * Tasks are Scott-encoded: task(cases) where cases = { pure, fail, httpGet, httpPost }
 *
 * @param {Function} task - Scott-encoded Task value
 * @param {Function} onSuccess - Called with result when task completes successfully
 * @param {Function} onError - Called with error message when task fails
 */
const MAX_TASK_DEPTH = 1000;

function executeTask(task, onSuccess, onError, _depth = 0) {
  if (_depth > MAX_TASK_DEPTH) {
    onError('Task recursion depth exceeded (possible infinite pure/fail chain)');
    return;
  }
  task({
    'pure': (value) => onSuccess(value),
    'fail': (error) => onError(error),
    'httpGet': (url, onOk, onErr) => {
      fetch(url)
        .then((response) => {
          if (!response.ok) throw new Error(`HTTP ${response.status}`);
          return response.text();
        })
        .then((text) => executeTask(onOk(text), onSuccess, onError, _depth + 1))
        .catch((error) => executeTask(onErr(error.message), onSuccess, onError, _depth + 1));
    },
    'httpPost': (url, body, onOk, onErr) => {
      fetch(url, { method: 'POST', headers: { 'Content-Type': detectContentType(body) }, body })
        .then((response) => {
          if (!response.ok) throw new Error(`HTTP ${response.status}`);
          return response.text();
        })
        .then((text) => executeTask(onOk(text), onSuccess, onError, _depth + 1))
        .catch((error) => executeTask(onErr(error.message), onSuccess, onError, _depth + 1));
    }
  });
}

/**
 * Execute a Cmd (side effect).
 * Commands are Scott-encoded: cmd(cases) where cases include DOM operations,
 * HTTP requests, clipboard, localStorage, routing, etc.
 *
 * @param {Function|null} cmd - Scott-encoded Cmd value, or null for no-op
 * @param {Function} dispatch - Function to dispatch resulting messages
 */
function executeCmd(cmd, dispatch) {
  if (!cmd) return;

  try { cmd({
    'ε': () => {},
    // Cmd errors are fire-and-forget: logged but not propagated back to the
    // Agda model. This is intentional — Cmd is a side-effect channel, not a
    // result-producing operation. Use Task/attempt for fallible operations.
    '_<>_': (cmd1, cmd2) => {
      try { executeCmd(cmd1, dispatch); } catch (e) { console.error('Cmd error:', e); }
      try { executeCmd(cmd2, dispatch); } catch (e) { console.error('Cmd error:', e); }
    },
    'delay': (ms, msg) => {
      const msNum = ensureNumber(ms);
      setTimeout(() => dispatch(msg), msNum);
    },
    'httpGet': (url, onSuccess, onError) => {
      fetch(url)
        .then((r) => r.ok ? r.text() : Promise.reject(new Error(`HTTP ${r.status}`)))
        .then((text) => dispatch(onSuccess(text)))
        .catch((error) => dispatch(onError(error.message)));
    },
    'httpPost': (url, body, onSuccess, onError) => {
      fetch(url, { method: 'POST', headers: { 'Content-Type': detectContentType(body) }, body })
        .then((r) => r.ok ? r.text() : Promise.reject(new Error(`HTTP ${r.status}`)))
        .then((text) => dispatch(onSuccess(text)))
        .catch((error) => dispatch(onError(error.message)));
    },
    'attempt': (task, handler) => {
      executeTask(
        task,
        (value) => dispatch(handler((cb) => cb['ok'](value))),
        (error) => dispatch(handler((cb) => cb['err'](error)))
      );
    },
    'focus': (sel) => {
      try {
        const el = document.querySelector(sel);
        if (el) el.focus();
        else console.warn(`Cmd.focus: element not found: "${sel}"`);
      } catch (e) {
        console.warn(`Cmd.focus: invalid selector: "${sel}"`, e.message);
      }
    },
    'blur': (sel) => {
      try {
        const el = document.querySelector(sel);
        if (el) el.blur();
        else console.warn(`Cmd.blur: element not found: "${sel}"`);
      } catch (e) {
        console.warn(`Cmd.blur: invalid selector: "${sel}"`, e.message);
      }
    },
    'scrollTo': (x, y) => window.scrollTo(ensureNumber(x), ensureNumber(y)),
    'scrollIntoView': (sel) => {
      try {
        const el = document.querySelector(sel);
        if (el) el.scrollIntoView({ behavior: 'smooth' });
        else console.warn(`Cmd.scrollIntoView: element not found: "${sel}"`);
      } catch (e) {
        console.warn(`Cmd.scrollIntoView: invalid selector: "${sel}"`, e.message);
      }
    },
    'writeClipboard': (text) => navigator.clipboard.writeText(text).catch((e) => {
      console.warn('Cmd.writeClipboard failed:', e.message);
    }),
    'readClipboard': (handler) => navigator.clipboard.readText()
      .then((t) => dispatch(handler(t)))
      .catch((e) => {
        console.warn('Cmd.readClipboard failed:', e.message);
        dispatch(handler(''));
      }),
    'getItem': (key, handler) => {
      const value = localStorage.getItem(key);
      dispatch(handler(value !== null ? (cb) => cb['just'](value) : (cb) => cb['nothing']()));
    },
    'setItem': (key, value) => localStorage.setItem(key, value),
    'removeItem': (key) => localStorage.removeItem(key),
    'wsSend': (url, message) => {
      const urlConns = wsConnections.get(url);
      if (!urlConns || urlConns.size === 0) {
        console.warn(`Cmd.wsSend: no WebSocket connection for "${url}"`);
        return;
      }
      let sent = false;
      for (const ws of urlConns.values()) {
        if (ws.readyState === WebSocket.OPEN) {
          ws.send(message);
          sent = true;
        }
      }
      if (!sent) {
        console.warn(`Cmd.wsSend: no open WebSocket for "${url}"`);
      }
    },
    'channelSend': (scriptUrl, message) => {
      const worker = channelConnections.get(scriptUrl);
      if (!worker) {
        console.warn(`Cmd.channelSend: no worker channel for "${scriptUrl}"`);
        return;
      }
      worker.postMessage(message);
    },
    'freeBuffer': (handle) => {
      const { id } = extractBufferHandle(handle);
      bufferRegistry.free(id);
    },
    'touchBuffer': (handle, handler) => {
      const { id, width, height } = extractBufferHandle(handle);
      const newVersion = bufferRegistry.touch(id);
      if (newVersion !== -1) {
        dispatch(handler(mkBufferHandle(id, newVersion, width, height)));
      } else {
        console.warn(`Cmd.touchBuffer: buffer ${id} not found`);
      }
    },
    'pushUrl': (url) => history.pushState(null, '', '#' + url),
    'replaceUrl': (url) => history.replaceState(null, '', '#' + url),
    'back': () => history.back(),
    'forward': () => history.forward()
  }); } catch (e) { console.error('executeCmd: unknown or failed command:', e.message || e); }
}

/**
 * Import NodeModule for binding/node extraction
 */
let NodeModule = null;

async function loadNodeModule() {
  if (NodeModule) return NodeModule;
  try {
    const mod = await import('../_build/jAgda.Agdelte.Reactive.Node.mjs');
    NodeModule = mod.default;
    return NodeModule;
  } catch (e) {
    console.error('Failed to load Node module:', e);
    throw e;
  }
}

// ─────────────────────────────────────────────────────────────────────
// Mutable model wrappers (in-place mutation via lenses)
// ─────────────────────────────────────────────────────────────────────

/** Get slots from model */
function getSlots(model) {
  if (model && model._slots) return model._slots;
  return probeSlots(model);
}

/** Get constructor name from model */
function getCtor(model) {
  if (model && model._ctor) return model._ctor;
  return probeCtor(model);
}

/** Set slot value (mutates in-place) */
function setSlot(model, idx, value) {
  if (model && model._slots) {
    model._slots[idx] = value;
  } else {
    throw new Error('Model not mutable — wrap first');
  }
}

/**
 * Wrap a Scott-encoded model for in-place mutation.
 * Creates a wrapper with _slots array that can be mutated.
 * Supports both function and object Agda→JS formats.
 */
function wrapMutable(model, _visited) {
  // Already mutable
  if (model && model._slots) return model;

  // Primitive or null — return as-is
  if (model === null || model === undefined) return model;
  if (typeof model !== 'function' && typeof model !== 'object') return model;

  // Cycle / shared-reference detection: use WeakMap so that if two model
  // slots reference the same sub-object, the second reference gets the
  // already-wrapped version instead of the unwrapped original.
  if (!_visited) _visited = new WeakMap();
  if (_visited.has(model)) return _visited.get(model);

  const args = probeSlots(model);
  const ctor = probeCtor(model);
  if (!args || !ctor) return model;

  // Create wrapper and register in _visited BEFORE recursive wrapping
  // to handle self-referential models (slot references parent).
  // The closure reads `slots` at call time, so filling them after
  // registration is safe — by the time anyone calls the wrapper,
  // all slots will be populated.
  const slots = [];
  let wrapper;
  if (typeof model === 'function') {
    wrapper = (cases) => cases[ctor](...slots);
  } else {
    wrapper = { [ctor]: (c) => c[ctor](...slots) };
  }
  wrapper._slots = slots;
  wrapper._ctor = ctor;
  _visited.set(model, wrapper);

  // Recursively wrap nested structures (cycles resolve via _visited)
  for (const a of args) {
    slots.push(
      (typeof a === 'function' || (typeof a === 'object' && a !== null))
        ? wrapMutable(a, _visited)
        : a
    );
  }

  return wrapper;
}

/** Ensure model is mutable (wrap if needed) */
function ensureMutable(model) {
  if (model && model._slots) return model;
  return wrapMutable(model);
}

/**
 * Deep-clone a slot value for snapshotting (used to protect against in-place mutation).
 */
function cloneSlot(s) {
  // Recognize mutable wrappers by _slots/_ctor (both function-format and object-format)
  if (s && s._slots && s._ctor) {
    const clonedSlots = s._slots.map(c => {
      if (c && c._slots && c._ctor) return cloneSlot(c);
      if (typeof c === 'object' && c !== null) {
        try { return structuredClone(c); } catch { return c; }
      }
      return c;
    });
    const ctor = s._ctor;
    if (typeof s === 'function') {
      const w = (cases) => cases[ctor](...clonedSlots);
      w._slots = clonedSlots;
      w._ctor = ctor;
      return w;
    } else {
      // Object-format wrapper: { [ctor]: (c) => c[ctor](...slots) }
      const w = { [ctor]: (c) => c[ctor](...clonedSlots) };
      w._slots = clonedSlots;
      w._ctor = ctor;
      return w;
    }
  }
  if (!s) return s;
  if (typeof s === 'object' && s !== null) {
    try { return structuredClone(s); } catch { return s; }
  }
  return s;
}

/**
 * Reconcile: copy changed slots from newModel into oldModel in-place.
 * Returns oldModel (mutated) if possible, or newModel if can't reconcile.
 */
function reconcile(oldModel, newModel) {
  // Can't reconcile if old model not mutable
  if (!oldModel || !oldModel._slots) {
    return wrapMutable(newModel);
  }

  const newSlots = getSlots(newModel);
  if (!newSlots) return wrapMutable(newModel);

  // Check constructor match before reconciling
  const newCtor = getCtor(newModel);
  if (!newCtor || oldModel._ctor !== newCtor) {
    return wrapMutable(newModel);
  }

  const oldSlots = oldModel._slots;

  // Structure changed (different arity) — can't reconcile
  if (oldSlots.length !== newSlots.length) {
    return wrapMutable(newModel);
  }

  // Copy changed slots in-place
  for (let i = 0; i < oldSlots.length; i++) {
    if (oldSlots[i] !== newSlots[i]) {
      // Recursively ensure nested structures are mutable
      const v = newSlots[i];
      oldSlots[i] = (typeof v === 'function' || (typeof v === 'object' && v !== null))
        ? wrapMutable(v)
        : v;
    }
  }

  return oldModel;  // same reference, mutated
}


// ─────────────────────────────────────────────────────────────────────
// Binding Scopes
// ─────────────────────────────────────────────────────────────────────

function createScope(parent) {
  const scope = {
    bindings: [],       // { node, binding, lastValue, slots }
    attrBindings: [],   // { node, binding, attrName, lastValue, slots }
    styleBindings: [],  // { node, binding, styleName, lastValue, slots }
    conditionals: [],   // { cond, innerNode, node, rendered, scope }
    lists: [],          // { marker, getList, render, renderedItems, keyed, keyFn }
    children: [],       // child scopes
    parent: parent || null,
    numSlots: -1,       // cached slot count (-1 = not yet detected)
    abortCtrl: new AbortController()  // for cleaning up event listeners
  };
  if (parent) parent.children.push(scope);
  return scope;
}

function destroyScope(scope) {
  // Copy children array since destroyScope mutates parent.children via splice
  const children = [...scope.children];
  for (const child of children) {
    destroyScope(child);
  }
  // Remove from parent
  if (scope.parent) {
    const idx = scope.parent.children.indexOf(scope);
    if (idx !== -1) scope.parent.children.splice(idx, 1);
  }
  // Cancel pending transition timeouts to prevent memory leaks
  for (const cond of scope.conditionals) {
    if (cond.enterTimeoutId) {
      clearTimeout(cond.enterTimeoutId);
      cond.enterTimeoutId = null;
    }
    if (cond.leaveTimeoutId) {
      clearTimeout(cond.leaveTimeoutId);
      cond.leaveTimeoutId = null;
    }
  }
  // Cancel pending animation RAF to prevent memory leaks
  for (const b of scope.styleBindings) {
    if (b.node && b.node._pendingAnimationRaf) {
      cancelAnimationFrame(b.node._pendingAnimationRaf);
      b.node._pendingAnimationRaf = null;
    }
  }
  // Abort all event listeners registered via this scope's signal
  scope.abortCtrl.abort();
  // Clear all arrays
  scope.bindings.length = 0;
  scope.attrBindings.length = 0;
  scope.styleBindings.length = 0;
  scope.conditionals.length = 0;
  scope.lists.length = 0;
  scope.children.length = 0;
}

/**
 * Create reactive app runner
 */
export async function runReactiveApp(moduleExports, container, options = {}) {
  await loadNodeModule();

  // Extract app record
  const appRecord = moduleExports.app;

  // Extract ReactiveApp fields (mutable for hot reload)
  const init = NodeModule.ReactiveApp.init(appRecord);
  let update = NodeModule.ReactiveApp.update(appRecord);
  let template = NodeModule.ReactiveApp.template(appRecord);
  let cmdFunc = NodeModule.ReactiveApp.cmd(appRecord);
  let subsFunc = NodeModule.ReactiveApp.subs(appRecord);

  // State — wrap model for in-place mutation
  let model = wrapMutable(init);
  const rootScope = createScope(null);
  let currentScope = rootScope;
  let currentNs = null;  // null = HTML, SVG_NS, or MATHML_NS

  let currentSubscription = null;
  let currentEventFingerprint = null;
  let isUpdating = false;
  const afterUpdateCallbacks = [];  // registered by glCanvas nodes

  // ─── Web Worker for Update ───────────────────────────────────────────
  // Optional: offload update function to worker thread
  let updateWorker = null;
  let workerReady = false;
  let workerPendingCallbacks = new Map();  // msgId → callback
  let workerMsgId = 0;

  /**
   * Initialize update worker (optional, explicit opt-in).
   * Moves the Agda `update` function to a Web Worker for CPU-intensive updates.
   * After init, `dispatch` sends messages to the worker which applies `update`
   * off the main thread and posts the new model back.
   * Usage: `app.initUpdateWorker('../_build/jAgda.MyApp.mjs')`
   * @param {string} modulePath - Path to the compiled Agda module
   */
  async function initUpdateWorker(modulePath) {
    return new Promise((resolve, reject) => {
      try {
        updateWorker = new Worker(new URL('./update-worker.js', import.meta.url), {
          type: 'module'
        });

        let initSettled = false;  // guard against double resolve/reject (rec #15)

        updateWorker.onmessage = (event) => {
          const { type, model: resultModel, message } = event.data;

          switch (type) {
            case 'ready':
              workerReady = true;
              if (!initSettled) { initSettled = true; resolve(); }
              break;

            case 'result': {
              // Find and invoke pending callback
              const id = event.data.id;
              const pending = workerPendingCallbacks.get(id);
              if (pending) {
                workerPendingCallbacks.delete(id);
                pending.resolve(resultModel);
              }
              break;
            }

            case 'error': {
              console.error('Update worker error:', message);
              // Resolve pending callback on error to prevent hanging promises
              const errId = event.data.id;
              if (errId !== undefined) {
                const pending = workerPendingCallbacks.get(errId);
                if (pending) {
                  workerPendingCallbacks.delete(errId);
                  pending.resolve(update(pending.msg)(pending.snapshotModel));  // fallback to main thread
                }
              }
              // Reject if still initializing (only once)
              if (!workerReady && !initSettled) { initSettled = true; reject(new Error(message)); }
              break;
            }
          }
        };

        updateWorker.onerror = (error) => {
          console.error('Update worker failed:', error);
          // Resolve all pending callbacks to prevent hanging promises
          for (const [, pending] of workerPendingCallbacks) {
            pending.resolve(null);
          }
          workerPendingCallbacks.clear();
          updateWorker = null;
          if (!workerReady && !initSettled) { initSettled = true; reject(error); }
        };

        // Initialize worker with module path
        updateWorker.postMessage({ type: 'init', modulePath });
      } catch (error) {
        console.warn('Web Worker not available, falling back to main thread:', error.message);
        resolve();  // Don't fail, just use main thread
      }
    });
  }

  // ─── Priority Scheduling ──────────────────────────────────────────────
  // P0 (Immediate): keyboard, focus - processed synchronously
  // P1 (Normal): clicks, user input - batched per animation frame
  // P2 (Background): data fetches, timers - processed in idle time
  const PRIORITY = { IMMEDIATE: 0, NORMAL: 1, BACKGROUND: 2 };

  // Priority queues
  let p1Queue = [];  // Normal priority (rAF batching)
  let p2Queue = [];  // Background priority (idle callback)
  let p1Scheduled = false;
  let p1RafId = 0;   // rAF ID for flushP1 — needed for cancellation on destroy
  let p2Scheduled = false;
  let destroyed = false;
  const MAX_BATCH_SIZE = 10000;
  let _droppedP1 = 0, _droppedP2 = 0;

  /**
   * Execute renderNode within a specific scope
   */
  function withScope(scope, fn) {
    const prev = currentScope;
    currentScope = scope;
    try {
      return fn();
    } finally {
      currentScope = prev;
    }
  }

  /**
   * Process a batch of messages and update DOM
   */
  let _batchDepth = 0;
  const MAX_BATCH_DEPTH = 100;

  /**
   * Apply a batch of messages: run cmds, update model, reconcile scope, and
   * refresh subscriptions. Extracted as a helper to avoid duplication between
   * the main batch and the deferred-immediate loop (rec #18).
   */
  function applyBatch(msgs) {
    const oldModel = model;
    const oldSlots = model && model._slots ? model._slots.map(s =>
      (s && s._slots && s._ctor) ? cloneSlot(s) : s
    ) : null;

    // Snapshot model before the batch so all cmdFunc calls see the
    // pre-batch state, not the post-update state from a prior message.
    // NOTE: This is intentional — all commands in a batch see the same
    // pre-batch model. If msg 1's cmd reads a field that msg 2's update
    // changes, cmd 2 still sees the old value. This prevents ordering
    // dependencies within a batch.
    const preBatchModel = model;

    for (const msg of msgs) {
      if (cmdFunc) {
        const cmd = cmdFunc(msg)(preBatchModel);
        executeCmd(cmd, dispatchImmediate);
      }
      const newModel = update(msg)(model);
      model = reconcile(model, newModel);
    }

    let effectiveOldModel = oldModel;
    if (oldSlots && oldModel._slots === model._slots) {
      effectiveOldModel = Object.create(oldModel);
      effectiveOldModel._slots = oldSlots;
    }

    updateScope(rootScope, effectiveOldModel, model);
    for (const cb of afterUpdateCallbacks) cb(effectiveOldModel, model);
    for (let i = afterUpdateCallbacks.length - 1; i >= 0; i--) {
      if (afterUpdateCallbacks[i]._dead) afterUpdateCallbacks.splice(i, 1);
    }
    updateSubscriptions();
  }

  function processBatch(msgs) {
    if (msgs.length === 0) return;
    if (_batchDepth >= MAX_BATCH_DEPTH) {
      console.warn('processBatch: max recursion depth (' + MAX_BATCH_DEPTH + ') exceeded, dropping ' + msgs.length + ' messages');
      return;
    }

    _batchDepth++;
    isUpdating = true;
    try {
      applyBatch(msgs);
    } finally {
      isUpdating = false;
    }
    _batchDepth--;
    // Process deferred immediate messages in same frame
    // (messages pushed to p1Queue by dispatchImmediate during isUpdating)
    // Loop instead of recursion to avoid stacking up to MAX_BATCH_DEPTH frames
    while (p1Queue.length > 0 && _batchDepth < MAX_BATCH_DEPTH) {
      const deferred = p1Queue;
      p1Queue = [];
      _batchDepth++;
      isUpdating = true;
      try {
        applyBatch(deferred);
      } finally {
        isUpdating = false;
      }
      _batchDepth--;
    }
  }

  /**
   * Flush P1 (normal priority) queue — runs on requestAnimationFrame
   */
  function flushP1() {
    if (destroyed || p1Queue.length === 0) {
      p1Scheduled = false;
      return;
    }

    const msgs = p1Queue;
    p1Queue = [];

    try {
      processBatch(msgs);
    } catch (e) {
      console.error('flushP1: batch processing failed:', e);
    }

    // If more messages arrived during flush, schedule another
    if (p1Queue.length > 0) {
      p1RafId = requestAnimationFrame(flushP1);
    } else {
      p1Scheduled = false;
    }
  }

  /**
   * Flush P2 (background priority) queue — runs on requestIdleCallback
   */
  function flushP2(deadline) {
    p2Scheduled = false;
    if (destroyed) return;

    // Process P2 messages one at a time, checking the deadline between each
    // to avoid exceeding the idle budget with DOM work from processBatch.
    const all = p2Queue;
    p2Queue = [];
    let i = 0;
    while (i < all.length && !destroyed && deadline.timeRemaining() > 1) {
      processBatch([all[i]]);
      i++;
    }
    // Put back unprocessed messages
    if (i < all.length) {
      p2Queue = all.slice(i).concat(p2Queue);
    }

    // If more messages remain, schedule another idle callback
    if (p2Queue.length > 0) {
      p2Scheduled = true;
      if (typeof requestIdleCallback !== 'undefined') {
        requestIdleCallback(flushP2, { timeout: 1000 });
      } else {
        // Fallback for Safari: use setTimeout with low priority
        setTimeout(() => flushP2({ timeRemaining: () => 50 }), 100);
      }
    }
  }

  /**
   * Dispatch with priority
   * @param {number} priority - PRIORITY.IMMEDIATE (0), NORMAL (1), or BACKGROUND (2)
   * @param {*} msg - Message to dispatch
   */
  function dispatchWithPriority(priority, msg) {
    switch (priority) {
      case PRIORITY.IMMEDIATE:
        dispatchImmediate(msg);
        break;
      case PRIORITY.NORMAL:
        dispatchNormal(msg);
        break;
      case PRIORITY.BACKGROUND:
        dispatchBackground(msg);
        break;
      default:
        dispatchNormal(msg);  // Default to normal
    }
  }

  /**
   * Dispatch message immediately (P0 - synchronous, no batching)
   * Use for keyboard input, focus events, or when immediate response is needed
   */
  function dispatchImmediate(msg) {
    if (destroyed) return;
    // If we're in the middle of a flush, add to P1 queue for next cycle
    if (isUpdating) {
      p1Queue.push(msg);
      return;
    }
    processBatch([msg]);
  }

  /**
   * Dispatch message with normal priority (P1 - batched per animation frame)
   * Use for clicks, user actions that can wait for next frame
   */
  function dispatchNormal(msg) {
    if (destroyed) return;
    if (p1Queue.length >= MAX_BATCH_SIZE) {
      _droppedP1++;
      console.error(`P1 queue overflow (>${MAX_BATCH_SIZE} messages, ${_droppedP1} dropped total). Check for infinite dispatch loops.`);
      return;
    }
    p1Queue.push(msg);
    if (!p1Scheduled) {
      p1Scheduled = true;
      p1RafId = requestAnimationFrame(flushP1);
    }
  }

  /**
   * Dispatch message with background priority (P2 - processed in idle time)
   * Use for data fetches, timers, and non-urgent updates
   */
  function dispatchBackground(msg) {
    if (destroyed) return;
    if (p2Queue.length >= MAX_BATCH_SIZE) {
      _droppedP2++;
      console.error(`P2 queue overflow (>${MAX_BATCH_SIZE} messages, ${_droppedP2} dropped total). Check for infinite dispatch loops.`);
      return;
    }
    p2Queue.push(msg);
    if (!p2Scheduled) {
      p2Scheduled = true;
      if (typeof requestIdleCallback !== 'undefined') {
        requestIdleCallback(flushP2, { timeout: 1000 });
      } else {
        // Fallback for Safari
        setTimeout(() => flushP2({ timeRemaining: () => 50 }), 100);
      }
    }
  }

  // Legacy aliases for backward compatibility
  const dispatch = dispatchNormal;
  const dispatchSync = dispatchImmediate;

  // Message wrapping for zoomRT scopes.
  // When rendering inside a zoomRT, dispatched messages are wrapped
  // through the composed wrap function chain.
  let currentMsgWrap = null;

  /**
   * Render a Node to DOM
   */
  function renderNode(node) {
    return node({
      text: (str) => document.createTextNode(str),

      bind: (binding) => {
        const extract = NodeModule.Binding.extract(binding);
        const value = extract(model);
        const textNode = document.createTextNode(value);
        // slots detected lazily on first update
        currentScope.bindings.push({ node: textNode, binding, lastValue: value, slots: null });
        return textNode;
      },

      elem: (tag, attrs, children) => {
        const prevNs = currentNs;

        // Entering namespace
        if (tag === 'svg') currentNs = SVG_NS;
        else if (tag === 'math') currentNs = MATHML_NS;

        // Create element in current namespace
        const el = currentNs
          ? document.createElementNS(currentNs, tag)
          : document.createElement(tag);

        // Exiting namespace (children go back to HTML)
        if (tag === 'foreignObject' || tag === 'annotation-xml') currentNs = null;

        try {
          const { items: attrArray } = listToArray(attrs);
          for (const attr of attrArray) {
            applyAttr(el, attr);
          }

          const { items: childArray } = listToArray(children);
          for (const child of childArray) {
            const childNode = renderNode(child);
            if (childNode) el.appendChild(childNode);
          }
        } finally {
          currentNs = prevNs;  // restore after subtree
        }
        return el;
      },

      empty: () => null,

      when: (cond, innerNode) => {
        const shouldShow = !!cond(model);

        if (shouldShow) {
          const childScope = createScope(currentScope);
          const rawRendered = withScope(childScope, () => renderNode(innerNode));
          const rendered = rawRendered || document.createComment('when-empty');
          currentScope.conditionals.push({
            cond, innerNode, node: rendered, rendered: true, scope: childScope
          });
          return rendered;
        } else {
          const placeholder = document.createComment('when');
          currentScope.conditionals.push({
            cond, innerNode, node: placeholder, rendered: false, scope: null
          });
          return placeholder;
        }
      },

      whenT: (cond, transition, innerNode) => {
        const shouldShow = !!cond(model);
        // Extract transition fields
        const enterClass = NodeModule.Transition.enterClass(transition);
        const leaveClass = NodeModule.Transition.leaveClass(transition);
        const duration = ensureNumber(NodeModule.Transition.duration(transition));

        if (shouldShow) {
          const childScope = createScope(currentScope);
          const rendered = withScope(childScope, () => renderNode(innerNode));
          // Apply enter class, remove on next frame
          if (rendered && rendered.classList) {
            rendered.classList.add(enterClass);
            requestAnimationFrame(() => {
              requestAnimationFrame(() => {
                if (rendered.classList) rendered.classList.remove(enterClass);
              });
            });
          }
          currentScope.conditionals.push({
            cond, innerNode, node: rendered, rendered: true, scope: childScope,
            transition: { enterClass, leaveClass, duration }
          });
          return rendered;
        } else {
          const placeholder = document.createComment('whenT');
          currentScope.conditionals.push({
            cond, innerNode, node: placeholder, rendered: false, scope: null,
            transition: { enterClass, leaveClass, duration }
          });
          return placeholder;
        }
      },

      foreach: (_typeA, getList, render) => {
        const container = document.createDocumentFragment();
        const marker = document.createComment('foreach');
        container.appendChild(marker);

        const items = getList(model);
        const renderedItems = [];
        const { items: itemArray, incomplete } = listToArray(items);

        itemArray.forEach((item, idx) => {
          const itemScope = createScope(currentScope);
          const itemNode = withScope(itemScope, () =>
            renderNode(render(item)(BigInt(idx)))
          );
          if (itemNode) {
            renderedItems.push({ item, node: itemNode, scope: itemScope });
            container.appendChild(itemNode);
          } else {
            // Null render — use placeholder to keep renderedItems aligned with item indices
            destroyScope(itemScope);
            const placeholder = document.createComment('empty');
            renderedItems.push({ item, node: placeholder, scope: null });
            container.appendChild(placeholder);
          }
        });

        if (incomplete) container.appendChild(makeTruncatedMarker());

        currentScope.lists.push({
          marker, getList, render, renderedItems,
          keyed: false, keyFn: null
        });

        return container;
      },

      scope: (fingerprint, innerNode) => {
        const childScope = createScope(currentScope);
        childScope.fingerprint = fingerprint;
        childScope.lastFP = fingerprint(model);
        return withScope(childScope, () => renderNode(innerNode));
      },

      scopeProj: (_typeM, proj, innerNode) => {
        const childScope = createScope(currentScope);
        childScope.project = proj;
        childScope.lastProj = proj(model);
        return withScope(childScope, () => renderNode(innerNode));
      },

      // zoomRT: runtime-deferred zoom (model projection + message wrapping).
      // Inner node's bindings expect the projected model type, so we
      // temporarily swap model and currentMsgWrap during rendering.
      zoomRT: (_typeM, _typeMsg, get, wrap, innerNode) => {
        const childScope = createScope(currentScope);
        childScope.modelTransform = get;
        childScope.project = get;
        childScope.lastProj = get(model);

        const savedModel = model;
        const savedWrap = currentMsgWrap;

        model = get(model);
        currentMsgWrap = savedWrap ? (msg) => savedWrap(wrap(msg)) : wrap;
        childScope.composedMsgWrap = currentMsgWrap;

        try {
          return withScope(childScope, () => renderNode(innerNode));
        } finally {
          model = savedModel;
          currentMsgWrap = savedWrap;
        }
      },

      foreachKeyed: (_typeA, getList, keyFn, render) => {
        const container = document.createDocumentFragment();
        const marker = document.createComment('foreachKeyed');
        container.appendChild(marker);

        const items = getList(model);
        const renderedItems = [];
        const { items: itemArray, incomplete } = listToArray(items);

        itemArray.forEach((item, idx) => {
          const key = keyFn(item);
          const itemScope = createScope(currentScope);
          const itemNode = withScope(itemScope, () =>
            renderNode(render(item)(BigInt(idx)))
          );
          if (itemNode) {
            renderedItems.push({ key, item, node: itemNode, scope: itemScope });
            container.appendChild(itemNode);
          } else {
            destroyScope(itemScope);
            const placeholder = document.createComment('empty');
            renderedItems.push({ key, item, node: placeholder, scope: null });
            container.appendChild(placeholder);
          }
        });

        if (incomplete) container.appendChild(makeTruncatedMarker());

        currentScope.lists.push({
          marker, getList, render, renderedItems,
          keyed: true, keyFn
        });

        return container;
      },

      glCanvas: (_typeS, attrs, scene) => {
        const canvas = document.createElement('canvas');

        const { items: attrArray } = listToArray(attrs);
        for (const attr of attrArray) {
          applyAttr(canvas, attr);
        }

        // Store scene data and app hooks for reactive-gl.js
        canvas.__glScene = scene;
        canvas.__glDispatch = dispatch;
        canvas.__glGetModel = () => model;

        // Register afterUpdate callback for this canvas.
        // reactive-gl.js will replace this with the real GL scope updater.
        canvas.__glUpdate = null;
        const glCallback = (oldModel, newModel) => {
          if (!canvas.isConnected) { glCallback._dead = true; return; }
          if (canvas.__glUpdate) canvas.__glUpdate(oldModel, newModel);
        };
        afterUpdateCallbacks.push(glCallback);

        return canvas;
      }
    });
  }

  /**
   * Set attribute with namespace support
   */
  function setAttr(el, name, value) {
    const ns = ATTR_NS[name];
    if (ns) {
      el.setAttributeNS(ns, name, value);
    } else if (BOOL_ATTRS.has(name)) {
      if (value === 'true' || value === true) el.setAttribute(name, '');
      else el.removeAttribute(name);
    } else if (name === 'value' && 'value' in el) {
      // For input/textarea/select, set the property (not attribute) to update displayed value
      el.value = value;
    } else {
      el.setAttribute(name, value);
    }
  }

  /**
   * Apply attribute to element
   */
  function applyAttr(el, attr) {
    // Capture current message wrap for zoomRT support.
    // Event handlers registered here will apply this wrap at dispatch time.
    const capturedWrap = currentMsgWrap;
    const sendNormal = capturedWrap
      ? (msg) => dispatchNormal(capturedWrap(msg))
      : dispatchNormal;
    const sendImmediate = capturedWrap
      ? (msg) => dispatchImmediate(capturedWrap(msg))
      : dispatchImmediate;

    attr({
      attr: (name, value) => {
        setAttr(el, name, value);
      },
      attrBind: (name, binding) => {
        const extract = NodeModule.Binding.extract(binding);
        const value = extract(model);
        setAttr(el, name, value);
        currentScope.attrBindings.push({ node: el, binding, attrName: name, lastValue: value, slots: null });
      },
      on: (event, msg) => {
        el.addEventListener(event, (e) => {
          if (el.tagName === 'A' && event === 'click') {
            e.preventDefault();
          }
          // Keyboard/focus events: P0 (immediate), clicks: P1 (normal)
          if (event === 'keydown' || event === 'keyup' || event === 'focus' || event === 'blur') {
            sendImmediate(msg);
          } else {
            sendNormal(msg);
          }
        }, { signal: currentScope.abortCtrl.signal });
      },
      onValue: (event, handler) => {
        el.addEventListener(event, (e) => {
          let value;
          if (event === 'keydown' || event === 'keyup') {
            value = e.key;
          } else if (event === 'wheel') {
            let dy = e.deltaY;
            if (e.deltaMode === 1) dy *= 40;
            else if (e.deltaMode === 2) dy *= window.innerHeight;
            value = String(dy);
            e.preventDefault();
          } else if (e.clientX !== undefined && e.clientY !== undefined) {
            // Pointer/mouse event - convert to SVG coords if in SVG
            const svg = el.closest('svg');
            const ctm = svg && svg.getScreenCTM && svg.getScreenCTM();
            if (ctm) {
              try {
                const svgPt = new DOMPoint(e.clientX, e.clientY).matrixTransform(ctm.inverse());
                value = svgPt.x + ',' + svgPt.y;
              } catch (err) {
                // Fallback if matrix transform fails (e.g., singular matrix)
                console.warn('SVG coordinate conversion failed, using screen coords:', err.message);
                value = e.clientX + ',' + e.clientY;
              }
            } else {
              // Not in SVG or CTM unavailable - use screen coordinates
              value = e.clientX + ',' + e.clientY;
            }
          } else {
            value = e.target.value || '';
          }
          // Keyboard events: P0 (immediate), others: P1 (normal)
          if (event === 'keydown' || event === 'keyup') {
            sendImmediate(handler(value));
          } else {
            sendNormal(handler(value));
          }
        }, event === 'wheel'
          ? { signal: currentScope.abortCtrl.signal, passive: false }
          : { signal: currentScope.abortCtrl.signal });
      },
      // Screen coordinates (no SVG conversion) - better for drag/pan
      onValueScreen: (event, handler) => {
        el.addEventListener(event, (e) => {
          let value;
          if (e.clientX !== undefined && e.clientY !== undefined) {
            value = e.clientX + ',' + e.clientY;
          } else {
            value = '0,0';
          }
          // Use priority dispatch for keyboard events
          if (event === 'keydown' || event === 'keyup') {
            sendImmediate(handler(value));
          } else {
            sendNormal(handler(value));
          }
        }, { signal: currentScope.abortCtrl.signal });
      },
      // Keyboard event filtered to specific keys; calls preventDefault
      onKeyFiltered: (keys, handler) => {
        const keyArray = listToArray(keys).items;
        el.addEventListener('keydown', (e) => {
          if (!keyArray.includes(e.key)) return;
          e.preventDefault();
          sendImmediate(handler(e.key));
        }, { signal: currentScope.abortCtrl.signal });
      },
      style: (name, value) => {
        el.style.setProperty(name, value);
      },
      styleBind: (name, binding) => {
        const extract = NodeModule.Binding.extract(binding);
        const value = extract(model);
        el.style.setProperty(name, value);
        currentScope.styleBindings.push({ node: el, binding, styleName: name, lastValue: value, slots: null });
      }
    });
  }

  /** Create a visible truncation marker for lists that exceed the iteration limit */
  function makeTruncatedMarker() {
    const el = document.createElement('li');
    el.className = 'agdelte-list-truncated';
    el.textContent = '[List truncated — exceeded iteration limit]';
    return el;
  }

  /** Add or remove the truncation marker on a list */
  function updateTruncatedMarker(list, parent, incomplete) {
    if (incomplete && !list._truncMarker) {
      list._truncMarker = makeTruncatedMarker();
      parent.appendChild(list._truncMarker);
    } else if (!incomplete && list._truncMarker) {
      list._truncMarker.remove();
      list._truncMarker = null;
    }
  }

  // ─────────────────────────────────────────────────────────────────
  // Scoped update
  // ─────────────────────────────────────────────────────────────────

  function updateScope(scope, oldModel, newModel) {
    updateScopeImmediate(scope, oldModel, newModel);
  }

  /**
   * Recursively update all bindings in a scope tree (immediate, no time-slicing).
   *
   * Optimization layers (checked in order):
   * 1. Fingerprint cutoff - skip if string fingerprint unchanged
   * 2. Slot-based tracking - skip if no tracked slots changed
   * 3. DeepEqual fallback - for non-record models
   *
   * @param {Object} scope - Scope object with bindings, children, etc.
   * @param {*} oldModel - Previous model value
   * @param {*} newModel - New model value
   */
  function updateScopeImmediate(scope, oldModel, newModel) {
    // zoomRT: apply model transformation and set up dispatch wrapping
    // for any renderNode calls during this scope's update (conditional show, list items)
    const savedModel = model;
    const savedWrap = currentMsgWrap;
    if (scope.modelTransform) {
      oldModel = scope.modelTransform(oldModel);
      newModel = scope.modelTransform(newModel);
      model = newModel;
      if (scope.composedMsgWrap) currentMsgWrap = scope.composedMsgWrap;
    }

    try {

    // Scope cutoff: string fingerprint only (scopeProj skipped if slot tracking active)
    if (scope.fingerprint) {
      const newFP = scope.fingerprint(newModel);
      if (newFP === scope.lastFP) return;
      scope.lastFP = newFP;
    }

    // Slot-based change detection (one Proxy probe, cached args)
    if (scope.numSlots === -1) scope.numSlots = countSlots(oldModel);
    const numSlots = scope.numSlots;
    let changed = null;
    if (numSlots > 0) {
      if (!scope.cachedArgs) scope.cachedArgs = probeSlots(oldModel);
      changed = changedSlotsFromCache(scope, newModel);
      // If slot tracking works and nothing changed, skip entire scope
      if (changed && changed.size === 0) return;
    } else if (scope.project) {
      // Fallback to deepEqual only when slot tracking unavailable (non-record model)
      const newProj = scope.project(newModel);
      if (deepEqual(scope.lastProj, newProj, 0)) return;
      scope.lastProj = newProj;
    }

    // Invalidate slot caches when constructor changes (same arity, different ctor)
    const newCtor = numSlots > 0 ? probeCtor(newModel) : null;
    const oldCtor = numSlots > 0 ? probeCtor(oldModel) : null;
    const ctorChanged = newCtor !== null && oldCtor !== null && newCtor !== oldCtor;

    // Lazy slot detection helper
    function ensureSlots(b) {
      if (ctorChanged) b.slots = null;  // invalidate on constructor change
      if (b.slots === null && numSlots > 0) {
        const extract = NodeModule.Binding.extract(b.binding);
        b.slots = detectSlots(extract, newModel, numSlots);
      }
    }

    // Text bindings
    for (const b of scope.bindings) {
      ensureSlots(b);
      if (changed && b.slots && !b.slots.some(s => changed.has(s))) continue;
      const extract = NodeModule.Binding.extract(b.binding);
      const newVal = extract(newModel);
      if (newVal !== b.lastValue) {
        b.node.textContent = newVal;
        b.lastValue = newVal;
      }
    }

    // Attribute bindings
    for (const b of scope.attrBindings) {
      ensureSlots(b);
      if (changed && b.slots && !b.slots.some(s => changed.has(s))) continue;
      const extract = NodeModule.Binding.extract(b.binding);
      const newVal = extract(newModel);
      if (newVal !== b.lastValue) {
        setAttr(b.node, b.attrName, newVal);
        b.lastValue = newVal;
      }
    }

    // Style bindings
    for (const b of scope.styleBindings) {
      ensureSlots(b);
      if (changed && b.slots && !b.slots.some(s => changed.has(s))) continue;
      const extract = NodeModule.Binding.extract(b.binding);
      const newVal = extract(newModel);
      if (newVal !== b.lastValue) {
        b.node.style.setProperty(b.styleName, newVal);
        b.lastValue = newVal;
      } else if (b.styleName === 'animation' && newVal !== 'none' && newVal !== '') {
        // Re-trigger same animation: browser ignores setting the same value,
        // so briefly clear and re-apply on next frame
        const el = b.node, val = newVal;
        // Cancel any pending animation reset to prevent race conditions
        if (el._pendingAnimationRaf) {
          cancelAnimationFrame(el._pendingAnimationRaf);
          el._pendingAnimationRaf = null;
        }
        el.style.animation = 'none';
        el._pendingAnimationRaf = requestAnimationFrame(() => {
          el._pendingAnimationRaf = null;
          if (el.isConnected) el.style.animation = val;
        });
      }
    }

    // Conditionals (when / whenT)
    for (const cond of scope.conditionals) {
      const showBool = !!cond.cond(newModel);

      if (showBool !== cond.rendered) {
        if (showBool) {
          // Cancel any pending leave transition timeout
          if (cond.leaveTimeoutId) {
            clearTimeout(cond.leaveTimeoutId);
            cond.leaveTimeoutId = null;
          }
          // Show: render into new child scope
          const childScope = createScope(scope);
          const newNode = withScope(childScope, () => renderNode(cond.innerNode));

          // Enter transition
          if (cond.transition && newNode && newNode.classList) {
            newNode.classList.add(cond.transition.enterClass);
            // Use duration if specified, otherwise remove on next frame
            if (cond.transition.duration > 0) {
              cond.enterTimeoutId = setTimeout(() => {
                cond.enterTimeoutId = null;
                if (newNode.classList) newNode.classList.remove(cond.transition.enterClass);
              }, cond.transition.duration);
            } else {
              requestAnimationFrame(() => {
                requestAnimationFrame(() => {
                  if (newNode.classList) newNode.classList.remove(cond.transition.enterClass);
                });
              });
            }
          }

          const replacement = newNode || document.createComment('when-empty');
          cond.node.replaceWith(replacement);
          cond.node = replacement;
          cond.rendered = true;
          cond.scope = childScope;
        } else {
          // Cancel any pending enter transition timeout
          if (cond.enterTimeoutId) {
            clearTimeout(cond.enterTimeoutId);
            cond.enterTimeoutId = null;
          }
          // Hide: destroy child scope
          if (cond.scope) destroyScope(cond.scope);

          if (cond.transition && cond.transition.duration > 0 && cond.node.classList) {
            // Leave transition: add class, wait, then remove
            const leaving = cond.node;
            leaving.classList.add(cond.transition.leaveClass);
            const placeholder = document.createComment(cond.transition ? 'whenT' : 'when');
            // Store timeout ID so it can be cancelled on destroy
            cond.leaveTimeoutId = setTimeout(() => {
              cond.leaveTimeoutId = null;
              if (leaving.parentNode) {
                leaving.replaceWith(placeholder);
                // Update tracking if this cond still points to leaving
                if (cond.node === leaving) cond.node = placeholder;
              }
            }, cond.transition.duration);
            // Immediately update tracking to placeholder for logic
            // but keep DOM node until transition ends
            cond.rendered = false;
            cond.scope = null;
          } else {
            const placeholder = document.createComment('when');
            cond.node.replaceWith(placeholder);
            cond.node = placeholder;
            cond.rendered = false;
            cond.scope = null;
          }
        }
      } else if (showBool && cond.scope) {
        // Condition unchanged, but update child scope bindings
        updateScopeImmediate(cond.scope, oldModel, newModel);
      }
    }

    // Lists (foreach / foreachKeyed)
    for (const list of scope.lists) {
      if (list.keyed) {
        updateKeyedList(scope, list, oldModel, newModel);
      } else {
        updateUnkeyedList(scope, list, oldModel, newModel);
      }
    }

    // Recurse into structural child scopes (scope / scopeProj).
    // Skip children owned by conditionals or lists — they're updated above.
    const ownedScopes = new Set();
    for (const cond of scope.conditionals) {
      if (cond.scope) ownedScopes.add(cond.scope);
    }
    for (const list of scope.lists) {
      for (const entry of list.renderedItems) {
        if (entry.scope) ownedScopes.add(entry.scope);
      }
    }
    for (const child of scope.children) {
      if (!ownedScopes.has(child)) {
        updateScopeImmediate(child, oldModel, newModel);
      }
    }

    } finally {
      // Restore model/dispatch state after zoomRT scope update (or on exception)
      if (scope.modelTransform) {
        model = savedModel;
        currentMsgWrap = savedWrap;
      }
    }
  }

  /**
   * Update unkeyed foreach list
   */
  function updateUnkeyedList(parentScope, list, oldModel, newModel) {
    const { items: newItems, incomplete } = listToArray(list.getList(newModel));
    const oldItems = list.renderedItems;
    const parent = list.marker.parentNode;
    if (!parent) return;

    // Greedy matching: reuse first min(old, new) items, remove extras, add new ones
    const minLen = Math.min(oldItems.length, newItems.length);

    // Update existing items (reuse scopes)
    for (let i = 0; i < minLen; i++) {
      if (oldItems[i].scope) {
        updateScopeImmediate(oldItems[i].scope, oldModel, newModel);
      }
    }

    // Remove extra old items
    for (let i = minLen; i < oldItems.length; i++) {
      oldItems[i].node.remove();
      if (oldItems[i].scope) destroyScope(oldItems[i].scope);
    }

    // Add new items — insert after last existing item
    const lastExisting = minLen > 0 ? oldItems[minLen - 1].node : list.marker;
    let insertBefore = lastExisting.nextSibling;
    for (let i = minLen; i < newItems.length; i++) {
      const itemScope = createScope(parentScope);
      const itemNode = withScope(itemScope, () =>
        renderNode(list.render(newItems[i])(BigInt(i)))
      );
      if (itemNode) {
        parent.insertBefore(itemNode, insertBefore);
        oldItems.push({ item: newItems[i], node: itemNode, scope: itemScope });
        insertBefore = itemNode.nextSibling;  // advance insertion point
      } else {
        // Null render — use placeholder to keep oldItems aligned with item indices
        destroyScope(itemScope);
        const placeholder = document.createComment('empty');
        parent.insertBefore(placeholder, insertBefore);
        oldItems.push({ item: newItems[i], node: placeholder, scope: null });
      }
    }

    // Truncate array if items were removed
    if (oldItems.length > newItems.length) {
      oldItems.length = newItems.length;
    }

    // Update truncation marker
    updateTruncatedMarker(list, parent, incomplete);
  }

  /**
   * Update keyed foreach list — key-based reconciliation
   */
  function updateKeyedList(parentScope, list, oldModel, newModel) {
    let { items: newItems, incomplete } = listToArray(list.getList(newModel));
    const oldItems = list.renderedItems;

    // Build old key map
    const oldKeyMap = new Map();
    for (let i = 0; i < oldItems.length; i++) {
      oldKeyMap.set(oldItems[i].key, oldItems[i]);
    }

    // Build new key set and deduplicate (keep last occurrence of each key)
    let newKeys = newItems.map(item => list.keyFn(item));
    {
      const seen = new Set();
      const duplicates = new Set();
      for (const key of newKeys) {
        if (seen.has(key)) duplicates.add(key);
        seen.add(key);
      }
      if (duplicates.size > 0) {
        console.warn(`foreachKeyed: duplicate keys detected: ${[...duplicates].join(', ')}. Keeping last occurrence of each.`);
        // Deduplicate: keep last occurrence by scanning from end
        const lastSeen = new Set();
        const keep = new Array(newItems.length).fill(false);
        for (let i = newItems.length - 1; i >= 0; i--) {
          if (!lastSeen.has(newKeys[i])) {
            lastSeen.add(newKeys[i]);
            keep[i] = true;
          }
        }
        const filteredItems = [];
        const filteredKeys = [];
        for (let i = 0; i < newItems.length; i++) {
          if (keep[i]) {
            filteredItems.push(newItems[i]);
            filteredKeys.push(newKeys[i]);
          }
        }
        newItems = filteredItems;
        newKeys = filteredKeys;
      }
    }

    // Check if anything changed
    const keysChanged = newKeys.length !== oldItems.length ||
      newKeys.some((key, i) => oldItems[i]?.key !== key);

    if (!keysChanged) {
      // Same keys in same order: just update bindings
      for (const entry of oldItems) {
        if (entry.scope) {
          updateScopeImmediate(entry.scope, oldModel, newModel);
        }
      }
      return;
    }

    // Keys changed: reconcile
    const parent = list.marker.parentNode;
    if (!parent) {
      console.warn('List marker not in DOM, skipping update');
      return;
    }
    const newRendered = [];
    const newKeySet = new Set(newKeys);

    // Remove items whose keys are no longer present
    for (const entry of oldItems) {
      if (!newKeySet.has(entry.key)) {
        entry.node.remove();
        if (entry.scope) destroyScope(entry.scope);
      }
    }

    // Remove all old items from DOM that will be reused (we'll re-insert in order)
    for (const entry of oldItems) {
      if (newKeySet.has(entry.key) && entry.node.parentNode) {
        entry.node.remove();
      }
    }

    // Use marker.nextSibling as stable insertion point AFTER all removals
    // This ensures correct positioning regardless of what was removed
    const insertBefore = list.marker.nextSibling;

    // Now insert in correct order (insertBefore was saved before removal)
    for (let i = 0; i < newItems.length; i++) {
      const key = newKeys[i];
      const oldEntry = oldKeyMap.get(key);

      if (oldEntry) {
        // Reuse existing DOM node
        parent.insertBefore(oldEntry.node, insertBefore);
        // Update bindings in existing scope
        if (oldEntry.scope) {
          updateScopeImmediate(oldEntry.scope, oldModel, newModel);
        }
        newRendered.push(oldEntry);
      } else {
        // New item: render fresh
        const itemScope = createScope(parentScope);
        const itemNode = withScope(itemScope, () =>
          renderNode(list.render(newItems[i])(BigInt(i)))
        );
        if (itemNode) {
          parent.insertBefore(itemNode, insertBefore);
          newRendered.push({ key, item: newItems[i], node: itemNode, scope: itemScope });
        } else {
          // Null render — use comment placeholder to track key, destroy unused scope
          destroyScope(itemScope);
          const placeholder = document.createComment('empty');
          parent.insertBefore(placeholder, insertBefore);
          newRendered.push({ key, item: newItems[i], node: placeholder, scope: null });
        }
      }
    }

    list.renderedItems = newRendered;

    // Update truncation marker
    if (parent) updateTruncatedMarker(list, parent, incomplete);
  }

  /**
   * Serialize event for comparison
   */
  function serializeEvent(event) {
    if (!event) return 'null';
    const cases = {
      never: () => 'never',
      sub: (subEvent) => `sub(${serializeEvent(subEvent)})`,
      interval: (ms, msg) => `interval(${ms})`,
      timeout: (ms, msg) => `timeout(${ms})`,
      animationFrame: (msg) => 'animationFrame',
      animationFrameWithTime: (handler) => 'animationFrameWithTime',
      springLoop: (cfg, onTick, onSettled) => {
        let pos, vel, tgt, stiff, damp;
        cfg({ mkSpringConfig: (p, v, t, s, d) => { pos = p; vel = v; tgt = t; stiff = s; damp = d; } });
        return `springLoop(${pos},${vel},${tgt},${stiff},${damp})`;
      },
      onKeyDown: (handler) => 'onKeyDown',
      onKeyUp: (handler) => 'onKeyUp',
      onMouseDown: (handler) => 'onMouseDown',
      onMouseUp: (handler) => 'onMouseUp',
      onMouseMove: (handler) => 'onMouseMove',
      onClick: (handler) => 'onClick',
      onKeys: (pairs) => {
        const pairArray = listToArray(pairs).items;
        const keys = [];
        for (const pair of pairArray) {
          let k;
          try {
            if (typeof pair === 'function') {
              pair({ '_,_': (a) => { k = a; } });
            } else if (pair && typeof pair['_,_'] === 'function') {
              pair['_,_']({ '_,_': (a) => { k = a; } });
            }
          } catch { /* ignore */ }
          if (k !== undefined) keys.push(k);
        }
        return `onKeys(${keys.join(',')})`;
      },
      httpGet: (url, ok, err) => `httpGet(${url})`,
      httpPost: (url, body, ok, err) => `httpPost(${url})`,
      merge: (e1, e2) => `merge(${serializeEvent(e1)},${serializeEvent(e2)})`,
      debounce: (ms, inner) => `debounce(${ms},${serializeEvent(inner)})`,
      throttle: (ms, inner) => `throttle(${ms},${serializeEvent(inner)})`,
      wsConnect: (url, handler) => `wsConnect(${url})`,
      onUrlChange: (handler) => 'onUrlChange',
      // Note: fingerprint uses only url+input, not callback identity.
      // Callbacks must be referentially stable across subs calls.
      worker: (url, input) => `worker(${url},${input})`,
      workerWithProgress: (url, input) => `workerWithProgress(${url},${input})`,
      parallel: (_typeB, eventList, mapFn) => 'parallel',
      race: (eventList) => 'race',
      poolWorker: (poolSize, url, input) => `poolWorker(${poolSize},${url},${input})`,
      poolWorkerWithProgress: (poolSize, url, input) => `poolWorkerWithProgress(${poolSize},${url},${input})`,
      workerChannel: (url) => `workerChannel(${url})`,
      allocShared: (n) => `allocShared(${n})`,
      workerShared: (buf, url, input) => `workerShared(${url},${input})`,
      allocImage: (w, h) => `allocImage(${w},${h})`,
      allocBuffer: (n) => `allocBuffer(${n})`,
      foldE: (_typeB, init, step, inner) => `foldE(${serializeEvent(inner)})`,
      mapFilterE: (_typeB, f, inner) => `mapFilterE(${serializeEvent(inner)})`,
      switchE: (initial, meta) => `switchE(${serializeEvent(initial)},${serializeEvent(meta)})`
    };
    const proxy = new Proxy(cases, {
      get: (target, prop) => target[prop] || ((...args) => {
        console.warn(`serializeEvent: unhandled Event constructor "${String(prop)}". Add it to serializeEvent cases.`);
        return `unknown(${String(prop)})`;
      })
    });
    return event(proxy);
  }

  /**
   * Update subscriptions
   */
  function updateSubscriptions() {
    if (!subsFunc) return;

    const eventSpec = subsFunc(model);
    const newFingerprint = serializeEvent(eventSpec);

    if (newFingerprint === currentEventFingerprint) return;

    if (currentSubscription) {
      unsubscribe(currentSubscription);
      currentSubscription = null;
    }

    try {
      currentSubscription = interpretEvent(eventSpec, dispatch, {
        immediate: dispatchImmediate,
        normal: dispatchNormal,
        background: dispatchBackground
      });
      currentEventFingerprint = newFingerprint;
    } catch (e) {
      console.error('updateSubscriptions: interpretEvent failed:', e);
      currentSubscription = null;
      currentEventFingerprint = null;
    }
  }

  // Count bindings for logging
  function countBindings(scope) {
    let text = scope.bindings.length;
    let attr = scope.attrBindings.length;
    let style = scope.styleBindings.length;
    for (const child of scope.children) {
      const c = countBindings(child);
      text += c.text;
      attr += c.attr;
      style += c.style;
    }
    return { text, attr, style };
  }

  // Initial render
  container.replaceChildren();
  const dom = renderNode(template);
  if (dom) {
    container.appendChild(dom);
    // Start SMIL animations (they don't auto-start when dynamically created)
    startSmilAnimations(container);
  }

  // Initial subscriptions
  updateSubscriptions();

  const counts = countBindings(rootScope);

  // ─────────────────────────────────────────────────────────────────
  // Big Lens — handle incoming peek/over WS messages
  // ─────────────────────────────────────────────────────────────────

  let bigLensWs = null;
  let bigLensClientId = null;
  let bigLensReconnectDelay = 0;
  let bigLensReconnectTimer = null;

  /**
   * Connect to Big Lens server for peek/over protocol.
   * Server assigns a client ID on connect.
   * Incoming messages:
   *   "peek:clientId"  → respond with JSON.stringify(model)
   *   "over:msgPayload" → dispatch msgPayload as a message
   *   "connected:clientId" → store our client ID
   *   "agentName:value" → agent broadcast (existing behavior)
   *
   * SECURITY: BigLens is a local development tool. Any WebSocket peer can
   * inject arbitrary messages via "over:" and read the full model via "peek:".
   * Do NOT expose the BigLens WebSocket port to untrusted networks.
   */
  function connectBigLens(wsUrl) {
    const ws = new WebSocket(wsUrl);
    bigLensWs = ws;

    ws.onmessage = (event) => {
      const data = event.data;

      if (data.startsWith('connected:')) {
        bigLensClientId = data.slice('connected:'.length);
        bigLensReconnectDelay = 0;  // reset backoff on successful connect
        return;
      }

      if (data.startsWith('peek:')) {
        // Server wants to read our model — respond with serialized model
        // Recursive serialization for Scott-encoded models
        const MAX_DEPTH = 64;
        const seen = new Set();
        const serializeModelValue = (m, depth = 0) => {
          if (m === null || m === undefined) return null;
          if (typeof m !== 'function' && typeof m !== 'object') return m;
          if (depth > MAX_DEPTH) return '[max depth]';
          if (typeof m === 'object' && seen.has(m)) return '[circular]';
          if (typeof m === 'object') seen.add(m);
          try {
            if (m._ctor && m._slots) {
              return { _ctor: m._ctor, _slots: m._slots.map(s => serializeModelValue(s, depth + 1)) };
            }
            const ctor = probeCtor(m);
            const slots = probeSlots(m);
            if (ctor && slots) {
              return { _ctor: ctor, _slots: slots.map(s => serializeModelValue(s, depth + 1)) };
            }
            return String(m);
          } finally {
            if (typeof m === 'object') seen.delete(m);
          }
        };
        const serialized = JSON.stringify(serializeModelValue(model));
        ws.send('peek-response:' + serialized);
        return;
      }

      if (data.startsWith('over:')) {
        // Server wants to dispatch a message to our app
        const msgPayload = data.slice('over:'.length);
        // Try to parse as JSON, fall back to raw string
        try {
          const msg = JSON.parse(msgPayload);
          dispatch(msg);
        } catch {
          // If not JSON, dispatch as raw string (for simple string messages)
          dispatch(msgPayload);
        }
        return;
      }

      // Otherwise: agent broadcast (existing behavior), ignore
    };

    ws.onerror = (e) => {
      console.warn('BigLens WebSocket error:', e.message || 'connection error');
    };

    ws.onclose = () => {
      bigLensClientId = null;
      bigLensWs = null;
      // Auto-reconnect with exponential backoff (cap at 30s)
      if (!destroyed) {
        bigLensReconnectDelay = Math.min((bigLensReconnectDelay || 500) * 2, 30000);
        bigLensReconnectTimer = setTimeout(() => {
          bigLensReconnectTimer = null;
          if (!destroyed) connectBigLens(wsUrl);
        }, bigLensReconnectDelay);
      }
    };

    return ws;
  }

  // Auto-connect if options specify a Big Lens WS URL
  if (options.bigLensWs) {
    connectBigLens(options.bigLensWs);
  }

  // ─────────────────────────────────────────────────────────────────
  // Time-Travel Debugging
  // ─────────────────────────────────────────────────────────────────

  let historyPast = [];      // previous models (newest first)
  let historyFuture = [];    // undone models (oldest first)
  const maxHistory = options.maxHistory || 100;

  // Recursive clone for Scott-encoded models — delegates to cloneSlot
  const cloneModel = cloneSlot;

  function timeTravelDispatch(msg) {
    // Record current state before update
    historyPast.unshift(cloneModel(model));
    if (historyPast.length > maxHistory) historyPast.length = maxHistory;
    historyFuture = []; // new action clears redo
    dispatch(msg);
  }

  function timeTravel_undo() {
    if (historyPast.length === 0) return;
    _batchDepth++;
    isUpdating = true;
    try {
      const oldModel = model;
      historyFuture.unshift(cloneModel(model));
      model = historyPast.shift();
      updateScope(rootScope, oldModel, model);
      for (const cb of afterUpdateCallbacks) cb(oldModel, model);
      for (let i = afterUpdateCallbacks.length - 1; i >= 0; i--) {
        if (afterUpdateCallbacks[i]._dead) afterUpdateCallbacks.splice(i, 1);
      }
      updateSubscriptions();
    } finally {
      isUpdating = false;
    }
    _batchDepth--;
    // Drain deferred immediate messages (same pattern as processBatch)
    while (p1Queue.length > 0 && _batchDepth < MAX_BATCH_DEPTH) {
      const deferred = p1Queue;
      p1Queue = [];
      _batchDepth++;
      isUpdating = true;
      try {
        applyBatch(deferred);
      } finally {
        isUpdating = false;
      }
      _batchDepth--;
    }
  }

  function timeTravel_redo() {
    if (historyFuture.length === 0) return;
    _batchDepth++;
    isUpdating = true;
    try {
      const oldModel = model;
      historyPast.unshift(cloneModel(model));
      model = historyFuture.shift();
      updateScope(rootScope, oldModel, model);
      for (const cb of afterUpdateCallbacks) cb(oldModel, model);
      for (let i = afterUpdateCallbacks.length - 1; i >= 0; i--) {
        if (afterUpdateCallbacks[i]._dead) afterUpdateCallbacks.splice(i, 1);
      }
      updateSubscriptions();
    } finally {
      isUpdating = false;
    }
    _batchDepth--;
    // Drain deferred immediate messages (same pattern as processBatch)
    while (p1Queue.length > 0 && _batchDepth < MAX_BATCH_DEPTH) {
      const deferred = p1Queue;
      p1Queue = [];
      _batchDepth++;
      isUpdating = true;
      try {
        applyBatch(deferred);
      } finally {
        isUpdating = false;
      }
      _batchDepth--;
    }
  }

  function timeTravel_getHistory() {
    return {
      past: historyPast.length,
      future: historyFuture.length,
      canUndo: historyPast.length > 0,
      canRedo: historyFuture.length > 0
    };
  }

  // ─────────────────────────────────────────────────────────────────
  // Hot Reload
  // ─────────────────────────────────────────────────────────────────

  function hotReload(newModuleExports) {
    const newAppRecord = newModuleExports.app;

    // Replace mutable function references
    update = NodeModule.ReactiveApp.update(newAppRecord);
    const newTemplate = NodeModule.ReactiveApp.template(newAppRecord);
    cmdFunc = NodeModule.ReactiveApp.cmd(newAppRecord);
    subsFunc = NodeModule.ReactiveApp.subs(newAppRecord);

    // Tear down old DOM
    if (currentSubscription) {
      unsubscribe(currentSubscription);
      currentSubscription = null;
      currentEventFingerprint = null;
    }
    destroyScope(rootScope);
    container.replaceChildren();
    afterUpdateCallbacks.length = 0;

    // Reset root scope — explicitly reset known properties to avoid
    // fragile delete-all-keys pattern that could leak non-enumerable props.
    const freshScope = createScope(null);
    rootScope.bindings = freshScope.bindings;
    rootScope.attrBindings = freshScope.attrBindings;
    rootScope.styleBindings = freshScope.styleBindings;
    rootScope.conditionals = freshScope.conditionals;
    rootScope.lists = freshScope.lists;
    rootScope.children = freshScope.children;
    rootScope.parent = freshScope.parent;
    rootScope.numSlots = freshScope.numSlots;
    rootScope.abortCtrl = freshScope.abortCtrl;
    rootScope.cachedArgs = undefined;
    rootScope.fingerprint = undefined;
    rootScope.lastFP = undefined;
    rootScope.project = undefined;
    rootScope.lastProj = undefined;

    // Terminate stale update worker — it holds a reference to the old module
    if (updateWorker) {
      for (const [, pending] of workerPendingCallbacks) {
        pending.resolve(null);
      }
      workerPendingCallbacks.clear();
      updateWorker.terminate();
      updateWorker = null;
      workerReady = false;
    }

    // Re-render with new template, preserving model
    template = newTemplate;
    const dom = renderNode(template);
    if (dom) {
      container.appendChild(dom);
      startSmilAnimations(container);
    }

    // Re-subscribe
    updateSubscriptions();

  }

  return {
    dispatch,           // batched (rAF)
    dispatchSync,       // immediate (no batching)
    getModel: () => model,
    getContainer: () => container,
    getClientId: () => bigLensClientId,
    connectBigLens,
    // Time-travel
    undo: timeTravel_undo,
    redo: timeTravel_redo,
    getHistory: timeTravel_getHistory,
    dispatchWithHistory: timeTravelDispatch,
    // Hot reload
    hotReload,
    // Worker-based update (optional)
    initUpdateWorker,
    destroy: () => {
      destroyed = true;
      // Cancel pending rAF to prevent flushP1 firing after destroy (rec #17)
      if (p1Scheduled && p1RafId) cancelAnimationFrame(p1RafId);
      p1Queue = [];
      p2Queue = [];
      p1Scheduled = false;
      p2Scheduled = false;
      if (currentSubscription) {
        unsubscribe(currentSubscription);
      }
      if (bigLensReconnectTimer) {
        clearTimeout(bigLensReconnectTimer);
        bigLensReconnectTimer = null;
      }
      if (bigLensWs) {
        bigLensWs.close();
      }
      if (updateWorker) {
        // Resolve pending callbacks before terminating to prevent promise leaks
        // and release references to snapshotModel
        for (const [, pending] of workerPendingCallbacks) {
          pending.resolve(null);
        }
        workerPendingCallbacks.clear();
        updateWorker.terminate();
        updateWorker = null;
      }
      destroyScope(rootScope);
      container.replaceChildren();
      afterUpdateCallbacks.length = 0;
    }
  };
}

/**
 * Mount with dynamic import
 */
export async function mountReactive(moduleName, container, options = {}) {
  const buildDir = options.buildDir || '../_build';
  const modulePath = `${buildDir}/jAgda.${moduleName}.mjs`;

  const containerEl = typeof container === 'string'
    ? document.querySelector(container)
    : container;

  if (!containerEl) {
    throw new Error(`Container not found: ${container}`);
  }

  try {
    const module = await import(modulePath);
    return await runReactiveApp(module.default, containerEl, options);
  } catch (e) {
    console.error(`Failed to load ${moduleName}:`, e);
    // Use textContent instead of innerHTML to prevent XSS
    containerEl.textContent = '';
    const div = document.createElement('div');
    div.className = 'error';
    const strong = document.createElement('strong');
    strong.textContent = `Failed to load ${moduleName}: `;
    div.appendChild(strong);
    div.appendChild(document.createTextNode(e.message));
    const pre = document.createElement('pre');
    pre.textContent = e.stack;
    div.appendChild(pre);
    containerEl.appendChild(div);
    throw e;
  }
}

export { interpretEvent, unsubscribe } from './events.js';

// Re-exported from agda-values.js for testing and external use
export { deepEqual, countSlots, detectSlots, probeCtor, probeSlots, changedSlotsFromCache } from './agda-values.js';
