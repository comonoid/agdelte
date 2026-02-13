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

// Namespaced attributes (xlink:href, xml:lang, etc.)
const ATTR_NS = {
  'xlink:href': 'http://www.w3.org/1999/xlink',
  'xlink:title': 'http://www.w3.org/1999/xlink',
  'xml:lang': 'http://www.w3.org/XML/1998/namespace',
  'xml:space': 'http://www.w3.org/XML/1998/namespace',
};

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
      fetch(url, { method: 'POST', headers: { 'Content-Type': 'text/plain' }, body })
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

  cmd({
    'ε': () => {},
    '_<>_': (cmd1, cmd2) => {
      executeCmd(cmd1, dispatch);
      executeCmd(cmd2, dispatch);
    },
    'delay': (ms, msg) => {
      const msNum = typeof ms === 'bigint' ? Number(ms) : Number(ms);
      setTimeout(() => dispatch(msg), msNum);
    },
    'httpGet': (url, onSuccess, onError) => {
      fetch(url)
        .then((r) => r.ok ? r.text() : Promise.reject(new Error(`HTTP ${r.status}`)))
        .then((text) => dispatch(onSuccess(text)))
        .catch((error) => dispatch(onError(error.message)));
    },
    'httpPost': (url, body, onSuccess, onError) => {
      fetch(url, { method: 'POST', headers: { 'Content-Type': 'text/plain' }, body })
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
    'scrollTo': (x, y) => window.scrollTo(Number(x), Number(y)),
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
    // Clipboard
    'clipboard': (text) => {
      navigator.clipboard.writeText(text).catch(err => console.warn('Clipboard write failed:', err));
    },
    'clipboardNotify': (text, onSuccess) => {
      navigator.clipboard.writeText(text)
        .then(() => dispatch(onSuccess('Copied!')))
        .catch(err => console.warn('Clipboard write failed:', err));
    },
    'wsSend': (url, message) => {
      const ws = wsConnections.get(url);
      if (!ws) {
        console.warn(`Cmd.wsSend: no WebSocket connection for "${url}"`);
        return;
      }
      if (ws.readyState !== WebSocket.OPEN) {
        console.warn(`Cmd.wsSend: WebSocket not open (state: ${ws.readyState})`);
        return;
      }
      ws.send(message);
    },
    'channelSend': (scriptUrl, message) => {
      const worker = channelConnections.get(scriptUrl);
      if (!worker) {
        console.warn(`Cmd.channelSend: no worker channel for "${scriptUrl}"`);
        return;
      }
      worker.postMessage(message);
    },
    'pushUrl': (url) => history.pushState(null, '', url),
    'replaceUrl': (url) => history.replaceState(null, '', url),
    'back': () => history.back(),
    'forward': () => history.forward()
  });
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
// Deep structural equality for Scott-encoded Agda values
// ─────────────────────────────────────────────────────────────────────

/**
 * Maximum nesting depth for deep equality comparison.
 * Models with deeper nesting will use reference equality for deep parts,
 * which causes unnecessary re-renders.
 */
const MAX_DEEP_EQUAL_DEPTH = 50;
let _deepEqualWarnCount = 0;
const _DEEP_EQUAL_WARN_INTERVAL = 100;

function deepEqual(a, b, depth) {
  if (a === b) return true;
  if (depth > MAX_DEEP_EQUAL_DEPTH) {
    _deepEqualWarnCount++;
    if (_deepEqualWarnCount === 1 || _deepEqualWarnCount % _DEEP_EQUAL_WARN_INTERVAL === 0) {
      console.warn(`deepEqual: max depth (${MAX_DEEP_EQUAL_DEPTH}) exceeded ${_deepEqualWarnCount} time(s), using reference equality. Consider flattening your model.`);
    }
    return false;
  }
  const ta = typeof a, tb = typeof b;
  if (ta !== tb) return false;
  if (ta !== 'function') return a === b;
  // Both are functions — probe as Scott-encoded values via Proxy
  let aCtor, aArgs, bCtor, bArgs;
  const probeA = new Proxy({}, {
    get(_, name) { return (...args) => { aCtor = name; aArgs = args; }; }
  });
  const probeB = new Proxy({}, {
    get(_, name) { return (...args) => { bCtor = name; bArgs = args; }; }
  });
  try {
    a(probeA);
    b(probeB);
  } catch {
    return false;  // not a Scott-encoded value
  }
  if (aCtor !== bCtor) return false;
  if (!aArgs || !bArgs || aArgs.length !== bArgs.length) return false;
  for (let i = 0; i < aArgs.length; i++) {
    if (!deepEqual(aArgs[i], bArgs[i], depth + 1)) return false;
  }
  return true;
}

// ─────────────────────────────────────────────────────────────────────
// Slot-based dependency tracking for Scott-encoded models
// ─────────────────────────────────────────────────────────────────────

/** Count slots (fields) of a Scott-encoded record */
function countSlots(model) {
  if (typeof model !== 'function') return 0;
  let count = 0;
  try {
    model(new Proxy({}, {
      get(_, name) { return (...args) => { count = args.length; }; }
    }));
  } catch { return 0; }
  return count;
}

/** Create a model with slot `idx` replaced by a unique sentinel */
function replaceSlot(model, idx) {
  const sentinel = Symbol();
  const replaced = (cases) => model(new Proxy({}, {
    get(_, ctorName) {
      return (...args) => {
        const modified = [...args];
        modified[idx] = sentinel;
        return cases[ctorName](...modified);
      };
    }
  }));
  return replaced;
}

/**
 * Detect which top-level model slots a binding's extract depends on.
 *
 * Algorithm: replace each slot with a unique Symbol sentinel, run extract.
 * If extract throws or returns different value, that slot is a dependency.
 *
 * Optimization: Most bindings depend on 1 slot. Once we find 2+ dependencies,
 * we return null (skip optimization, fall through to full check).
 *
 * Complexity: O(N) where N = number of slots. Called once per binding at setup.
 * For models with many fields (>20), consider using nested records.
 */
function detectSlots(extract, model, numSlots) {
  if (numSlots === 0) return null;

  // Get base value once
  let baseValue;
  try { baseValue = extract(model); } catch { return null; }

  // Fast path: probe slots until we find ≤1 dependency
  // If 2+ deps found, return null (too complex for slot optimization)
  let singleDep = -1;  // -1 = none found, ≥0 = slot index
  for (let i = 0; i < numSlots; i++) {
    const sentinel = Symbol();
    const replaced = (cases) => model(new Proxy({}, {
      get(_, ctorName) {
        return (...args) => {
          const modified = args.slice();
          modified[i] = sentinel;
          return cases[ctorName](...modified);
        };
      }
    }));

    let isDep = false;
    try {
      const modifiedValue = extract(replaced);
      isDep = modifiedValue !== baseValue;
    } catch {
      isDep = true; // if it throws, assume dependency
    }

    if (isDep) {
      if (singleDep >= 0) {
        // Found 2nd dependency - fall back to full check mode
        return null;
      }
      singleDep = i;
    }
  }

  return singleDep >= 0 ? [singleDep] : null;
}

/** Probe a Scott-encoded model, return its constructor args */
const _slotProbe = new Proxy({}, {
  get(_, name) { return (...args) => args; }
});

/**
 * Probe slots from Scott-encoded model.
 * Supports two Agda→JS formats:
 * 1. Function: model(cases) => cases["ctor"](a, b)
 * 2. Object: {ctor: (c) => c.ctor(a, b)}
 */
function probeSlots(model) {
  if (!model) return null;

  // Format 1: function
  if (typeof model === 'function') {
    try {
      const result = model(_slotProbe);
      return Array.isArray(result) ? result : null;
    } catch { return null; }
  }

  // Format 2: object with single method
  if (typeof model === 'object') {
    const keys = Object.keys(model);
    if (keys.length === 1 && typeof model[keys[0]] === 'function') {
      try { return model[keys[0]](_slotProbe); } catch { return null; }
    }
  }

  return null;
}

/**
 * Probe constructor name of a Scott-encoded value.
 * Supports both function and object formats.
 */
function probeCtor(model) {
  if (!model) return null;

  // Format 1: function
  if (typeof model === 'function') {
    let ctor = null;
    try {
      model(new Proxy({}, {
        get(_, name) { return (...args) => { ctor = name; }; }
      }));
    } catch { return null; }
    return ctor;
  }

  // Format 2: object with single method — key IS the ctor name
  if (typeof model === 'object') {
    const keys = Object.keys(model);
    if (keys.length === 1 && typeof model[keys[0]] === 'function') {
      return keys[0];
    }
  }

  return null;
}

// ─────────────────────────────────────────────────────────────────────
// Mutable model wrappers (in-place mutation via lenses)
// Supports both Scott-encoded functions and future tagged arrays
// ─────────────────────────────────────────────────────────────────────

/** Check if model is a tagged array (future compiler format) */
function isTaggedArray(model) {
  return Array.isArray(model) && typeof model[0] === 'string';
}

/** Get slots from any model format */
function getSlots(model) {
  if (isTaggedArray(model)) return model.slice(1);
  if (model && model._slots) return model._slots;
  return probeSlots(model);
}

/** Get constructor name from any model format */
function getCtor(model) {
  if (isTaggedArray(model)) return model[0];
  if (model && model._ctor) return model._ctor;
  return probeCtor(model);
}

/** Set slot value (mutates in-place) */
function setSlot(model, idx, value) {
  if (isTaggedArray(model)) {
    model[idx + 1] = value;  // +1 because arr[0] is tag
  } else if (model && model._slots) {
    model._slots[idx] = value;
  } else {
    throw new Error('Model not mutable — wrap first');
  }
}

/**
 * Wrap a Scott-encoded model for in-place mutation.
 * Creates a wrapper with _slots array that can be mutated.
 * Supports both function and object Agda→JS formats.
 * Tagged arrays are already mutable, returned as-is.
 */
function wrapMutable(model) {
  // Already mutable formats
  if (isTaggedArray(model)) return model;
  if (model && model._slots) return model;

  // Primitive or null — return as-is
  if (model === null || model === undefined) return model;
  if (typeof model !== 'function' && typeof model !== 'object') return model;

  const args = probeSlots(model);
  const ctor = probeCtor(model);
  if (!args || !ctor) return model;

  // Recursively wrap nested structures
  const slots = args.map(a =>
    (typeof a === 'function' || (typeof a === 'object' && a !== null))
      ? wrapMutable(a)
      : a
  );

  // Create wrapper based on original format
  let wrapper;
  if (typeof model === 'function') {
    // Function format: (cases) => cases[ctor](...slots)
    wrapper = (cases) => cases[ctor](...slots);
  } else {
    // Object format: {ctor: (c) => c.ctor(...slots)}
    wrapper = { [ctor]: (c) => c[ctor](...slots) };
  }

  wrapper._slots = slots;
  wrapper._ctor = ctor;
  return wrapper;
}

/** Ensure model is mutable (wrap if needed) */
function ensureMutable(model) {
  if (isTaggedArray(model)) return model;
  if (model && model._slots) return model;
  return wrapMutable(model);
}

/**
 * Reconcile: copy changed slots from newModel into oldModel in-place.
 * Returns oldModel (mutated) if possible, or newModel if can't reconcile.
 */
function reconcile(oldModel, newModel) {
  // Can't reconcile if old model not mutable
  if (!oldModel || !oldModel._slots) {
    return isTaggedArray(newModel) ? newModel : wrapMutable(newModel);
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
      oldSlots[i] = typeof newSlots[i] === 'function'
        ? wrapMutable(newSlots[i])
        : newSlots[i];
    }
  }

  return oldModel;  // same reference, mutated
}

/**
 * Detect which top-level slots changed between cached args and new model.
 * scope.cachedArgs stores previous probe result; updated in-place.
 * Returns a Set of changed slot indices, or null if not trackable.
 */
function changedSlotsFromCache(scope, newModel) {
  const newArgs = probeSlots(newModel);
  if (!newArgs) return null;
  const oldArgs = scope.cachedArgs;
  scope.cachedArgs = newArgs;
  if (!oldArgs || oldArgs.length !== newArgs.length) return null;
  const changed = new Set();
  for (let i = 0; i < oldArgs.length; i++) {
    if (oldArgs[i] !== newArgs[i]) changed.add(i);
  }
  return changed;
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
   * Initialize update worker (optional).
   * Call this for CPU-intensive update functions.
   * @param {string} modulePath - Path to the Agda module (e.g., '../_build/jAgda.Counter.mjs')
   */
  async function initUpdateWorker(modulePath) {
    return new Promise((resolve, reject) => {
      try {
        updateWorker = new Worker(new URL('./update-worker.js', import.meta.url), {
          type: 'module'
        });

        updateWorker.onmessage = (event) => {
          const { type, model: resultModel, message } = event.data;

          switch (type) {
            case 'ready':
              workerReady = true;
              resolve();
              break;

            case 'result': {
              // Find and invoke pending callback
              const id = event.data.id;
              const callback = workerPendingCallbacks.get(id);
              if (callback) {
                workerPendingCallbacks.delete(id);
                callback(resultModel);
              }
              break;
            }

            case 'error': {
              console.error('Update worker error:', message);
              // Resolve pending callback on error to prevent hanging promises
              const errId = event.data.id;
              if (errId !== undefined) {
                const cb = workerPendingCallbacks.get(errId);
                if (cb) {
                  workerPendingCallbacks.delete(errId);
                  cb(update(event.data.msg)(model));  // fallback to main thread
                }
              }
              // Reject if still initializing
              if (!workerReady) reject(new Error(message));
              break;
            }
          }
        };

        updateWorker.onerror = (error) => {
          console.error('Update worker failed:', error);
          // Resolve all pending callbacks to prevent hanging promises
          for (const [, cb] of workerPendingCallbacks) {
            cb(null);
          }
          workerPendingCallbacks.clear();
          updateWorker = null;
          if (!workerReady) reject(error);
        };

        // Initialize worker with module path
        updateWorker.postMessage({ type: 'init', modulePath });
      } catch (error) {
        console.warn('Web Worker not available, falling back to main thread:', error.message);
        resolve();  // Don't fail, just use main thread
      }
    });
  }

  /**
   * Run update in worker (if available) or main thread.
   * @param {*} msg - Message to process
   * @param {*} currentModel - Current model state
   * @returns {Promise<*>} - New model
   */
  function runUpdateAsync(msg, currentModel) {
    if (!updateWorker || !workerReady) {
      // Fallback to main thread
      return Promise.resolve(update(msg)(currentModel));
    }

    return new Promise((resolve) => {
      const id = workerMsgId++;
      workerPendingCallbacks.set(id, resolve);
      updateWorker.postMessage({ type: 'update', id, msg, model: currentModel });
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
  let p2Scheduled = false;
  const MAX_BATCH_SIZE = 10000;
  let _droppedP1 = 0, _droppedP2 = 0;

  /**
   * Execute renderNode within a specific scope
   */
  function withScope(scope, fn) {
    const prev = currentScope;
    currentScope = scope;
    const result = fn();
    currentScope = prev;
    return result;
  }

  /**
   * Process a batch of messages and update DOM
   */
  function processBatch(msgs) {
    if (msgs.length === 0) return;

    isUpdating = true;
    try {
      // Snapshot old slots before batch so reconcile's in-place mutation
      // doesn't alias oldModel with model
      const oldModel = model;
      const oldSlots = model && model._slots ? [...model._slots] : null;

      // Apply all messages sequentially
      for (const msg of msgs) {
        // Update model first, then execute command (Elm architecture order)
        const newModel = update(msg)(model);
        model = reconcile(model, newModel);
        // Execute command after update so cmd sees updated model
        if (cmdFunc) {
          const cmd = cmdFunc(msg)(model);
          executeCmd(cmd, dispatchImmediate);  // commands dispatch immediately
        }
      }

      // Use snapshotted slots for comparison so in-place mutation
      // doesn't cause oldModel === model
      let effectiveOldModel = oldModel;
      if (oldSlots && oldModel._slots === model._slots) {
        // reconcile mutated in-place — build a comparison proxy
        effectiveOldModel = Object.create(oldModel);
        effectiveOldModel._slots = oldSlots;
      }

      // ONE updateScope for all messages
      updateScope(rootScope, effectiveOldModel, model);

      // Update GL scopes (use effectiveOldModel so GL bindings see snapshotted slots)
      for (const cb of afterUpdateCallbacks) cb(effectiveOldModel, model);
      // Prune callbacks for disconnected canvases
      for (let i = afterUpdateCallbacks.length - 1; i >= 0; i--) {
        if (afterUpdateCallbacks[i]._dead) afterUpdateCallbacks.splice(i, 1);
      }

      // Update subscriptions
      updateSubscriptions();
    } finally {
      isUpdating = false;
    }

    // Process deferred immediate messages in same frame
    // (messages pushed to p1Queue by dispatchImmediate during isUpdating)
    if (p1Queue.length > 0) {
      const deferred = p1Queue;
      p1Queue = [];
      processBatch(deferred);
    }
  }

  /**
   * Flush P1 (normal priority) queue — runs on requestAnimationFrame
   */
  function flushP1() {
    p1Scheduled = false;
    if (p1Queue.length === 0) return;

    const msgs = p1Queue;
    p1Queue = [];

    processBatch(msgs);

    // If more messages arrived during flush, schedule another
    if (p1Queue.length > 0) {
      p1Scheduled = true;
      requestAnimationFrame(flushP1);
    }
  }

  /**
   * Flush P2 (background priority) queue — runs on requestIdleCallback
   */
  function flushP2(deadline) {
    p2Scheduled = false;

    // Batch P2 messages like P1 to avoid N×updateScope overhead
    const batch = [];
    while (p2Queue.length > 0 && deadline.timeRemaining() > 1) {
      batch.push(p2Queue.shift());
    }
    if (batch.length > 0) {
      processBatch(batch);
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
    if (p1Queue.length >= MAX_BATCH_SIZE) {
      _droppedP1++;
      console.error(`P1 queue overflow (>${MAX_BATCH_SIZE} messages, ${_droppedP1} dropped total). Check for infinite dispatch loops.`);
      return;
    }
    p1Queue.push(msg);
    if (!p1Scheduled) {
      p1Scheduled = true;
      requestAnimationFrame(flushP1);
    }
  }

  /**
   * Dispatch message with background priority (P2 - processed in idle time)
   * Use for data fetches, timers, and non-urgent updates
   */
  function dispatchBackground(msg) {
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
        const duration = Number(NodeModule.Transition.duration(transition));

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
    } else if (name === 'disabled' || name === 'checked') {
      if (value === 'true') el.setAttribute(name, '');
      else el.removeAttribute(name);
    } else {
      el.setAttribute(name, value);
    }
  }

  /**
   * Apply attribute to element
   */
  function applyAttr(el, attr) {
    attr({
      attr: (name, value) => {
        if (name === 'disabled' || name === 'checked') {
          if (value === 'true') el.setAttribute(name, '');
          else el.removeAttribute(name);
        } else {
          setAttr(el, name, value);
        }
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
            dispatchImmediate(msg);
          } else {
            dispatchNormal(msg);
          }
        }, { signal: currentScope.abortCtrl.signal });
      },
      onValue: (event, handler) => {
        el.addEventListener(event, (e) => {
          let value;
          if (event === 'keydown' || event === 'keyup') {
            value = e.key;
          } else if (event === 'wheel') {
            value = String(e.deltaY);
            e.preventDefault();
          } else if (e.clientX !== undefined && e.clientY !== undefined) {
            // Pointer/mouse event - convert to SVG coords if in SVG
            const svg = el.closest('svg');
            const ctm = svg && svg.getScreenCTM && svg.getScreenCTM();
            if (ctm) {
              try {
                const pt = svg.createSVGPoint();
                pt.x = e.clientX;
                pt.y = e.clientY;
                const svgPt = pt.matrixTransform(ctm.inverse());
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
            dispatchImmediate(handler(value));
          } else {
            dispatchNormal(handler(value));
          }
        }, { signal: currentScope.abortCtrl.signal });
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
            dispatchImmediate(handler(value));
          } else {
            dispatchNormal(handler(value));
          }
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
    el.className = 'agdelte-truncated';
    el.style.cssText = 'color:#f44;font-style:italic;list-style:none;padding:4px 0;';
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

  /**
   * Convert Agda list to JS array
   * @param {*} list - Agda List (native Array or Scott-encoded)
   * @returns {{ items: Array, incomplete: boolean }} - items and error flag
   */
  function listToArray(list) {
    if (!list) return { items: [], incomplete: false };
    if (Array.isArray(list)) return { items: list, incomplete: false };
    if (typeof list !== 'function') {
      console.warn('listToArray: expected function, got', typeof list, list);
      return { items: [], incomplete: true };
    }

    const result = [];
    let current = list;
    let incomplete = false;
    const MAX_LIST_ITERATIONS = 100000;
    let iterations = 0;
    while (true) {
      if (iterations++ > MAX_LIST_ITERATIONS) {
        console.error('listToArray: possible infinite loop (>100000 items or cyclic list)');
        incomplete = true;
        break;
      }
      if (typeof current !== 'function') {
        console.warn('listToArray: tail is not a function', current);
        incomplete = true;
        break;
      }
      const done = current({
        '[]': () => true,
        '_∷_': (head, tail) => {
          result.push(head);
          current = tail;
          return false;
        }
      });
      if (done) break;
    }
    return { items: result, incomplete };
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

    // Lazy slot detection helper
    function ensureSlots(b) {
      if (b.slots === null && numSlots > 0) {
        const extract = NodeModule.Binding.extract(b.binding);
        b.slots = detectSlots(extract, oldModel, numSlots);
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
          el.style.animation = val;
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
              setTimeout(() => {
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
    const { items: newItems, incomplete } = listToArray(list.getList(newModel));
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
        newItems.length = 0;
        newItems.push(...filteredItems);
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
    const parent = list.marker.parentNode;
    if (parent) updateTruncatedMarker(list, parent, incomplete);
  }

  /**
   * Serialize event for comparison
   */
  function serializeEvent(event) {
    if (!event) return 'null';
    return event({
      never: () => 'never',
      interval: (ms, msg) => `interval(${ms})`,
      timeout: (ms, msg) => `timeout(${ms})`,
      animationFrame: (msg) => 'animationFrame',
      animationFrameWithTime: (handler) => 'animationFrameWithTime',
      springLoop: (pos, vel, tgt, stiff, damp, onTick, onSettled) =>
        `springLoop(${pos},${vel},${tgt},${stiff},${damp})`,
      onKeyDown: (handler) => 'onKeyDown',
      onKeyUp: (handler) => 'onKeyUp',
      onKeys: (pairs) => 'onKeys',
      httpGet: (url, ok, err) => `httpGet(${url})`,
      httpPost: (url, body, ok, err) => `httpPost(${url})`,
      merge: (e1, e2) => `merge(${serializeEvent(e1)},${serializeEvent(e2)})`,
      debounce: (ms, inner) => `debounce(${ms})`,
      throttle: (ms, inner) => `throttle(${ms})`,
      wsConnect: (url, handler) => `wsConnect(${url})`,
      onUrlChange: (handler) => 'onUrlChange',
      worker: (url, input) => `worker(${url},${input})`,
      workerWithProgress: (url, input) => `workerWithProgress(${url},${input})`,
      parallel: (_typeB, eventList, mapFn) => 'parallel',
      race: (eventList) => 'race',
      poolWorker: (poolSize, url, input) => `poolWorker(${poolSize},${url},${input})`,
      poolWorkerWithProgress: (poolSize, url, input) => `poolWorkerWithProgress(${poolSize},${url},${input})`,
      workerChannel: (url) => `workerChannel(${url})`,
      allocShared: (n) => `allocShared(${n})`,
      workerShared: (buf, url, input) => `workerShared(${url},${input})`,
      foldE: (_typeB, init, step, inner) => `foldE(${serializeEvent(inner)})`,
      mapFilterE: (_typeB, f, inner) => `mapFilterE(${serializeEvent(inner)})`,
      switchE: (initial, meta) => `switchE(${serializeEvent(initial)},${serializeEvent(meta)})`
    });
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
    }

    currentSubscription = interpretEvent(eventSpec, dispatch, {
      immediate: dispatchImmediate,
      normal: dispatchNormal,
      background: dispatchBackground
    });
    currentEventFingerprint = newFingerprint;
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
  container.innerHTML = '';
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

  /**
   * Connect to Big Lens server for peek/over protocol.
   * Server assigns a client ID on connect.
   * Incoming messages:
   *   "peek:clientId"  → respond with JSON.stringify(model)
   *   "over:msgPayload" → dispatch msgPayload as a message
   *   "connected:clientId" → store our client ID
   *   "agentName:value" → agent broadcast (existing behavior)
   */
  function connectBigLens(wsUrl) {
    const ws = new WebSocket(wsUrl);
    bigLensWs = ws;

    ws.onmessage = (event) => {
      const data = event.data;

      if (data.startsWith('connected:')) {
        bigLensClientId = data.slice('connected:'.length);
        return;
      }

      if (data.startsWith('peek:')) {
        // Server wants to read our model — respond with serialized model
        // Recursive serialization for Scott-encoded models
        const serializeModelValue = (m) => {
          if (m === null || m === undefined) return null;
          if (typeof m !== 'function' && typeof m !== 'object') return m;
          if (m._ctor && m._slots) {
            return { _ctor: m._ctor, _slots: m._slots.map(serializeModelValue) };
          }
          const ctor = probeCtor(m);
          const slots = probeSlots(m);
          if (ctor && slots) {
            return { _ctor: ctor, _slots: slots.map(serializeModelValue) };
          }
          return String(m);
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

    ws.onclose = () => {
      bigLensClientId = null;
      bigLensWs = null;
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

  // Recursive clone for Scott-encoded models (functions can't be structuredClone'd)
  function cloneModel(m) {
    if (!m || typeof m !== 'function') return m;
    if (!m._slots || !m._ctor) return m;
    const clonedSlots = m._slots.map(s =>
      (typeof s === 'function' && s._slots && s._ctor) ? cloneModel(s) : s
    );
    const ctor = m._ctor;
    const w = (cases) => cases[ctor](...clonedSlots);
    w._slots = clonedSlots;
    w._ctor = ctor;
    return w;
  }

  function timeTravelDispatch(msg) {
    // Record current state before update
    historyPast.unshift(cloneModel(model));
    if (historyPast.length > maxHistory) historyPast.length = maxHistory;
    historyFuture = []; // new action clears redo
    dispatch(msg);
  }

  function timeTravel_undo() {
    if (historyPast.length === 0) return;
    const oldModel = model;
    historyFuture.unshift(cloneModel(model));
    model = historyPast.shift();
    updateScope(rootScope, oldModel, model);
    for (const cb of afterUpdateCallbacks) cb(oldModel, model);
    updateSubscriptions();
  }

  function timeTravel_redo() {
    if (historyFuture.length === 0) return;
    const oldModel = model;
    historyPast.unshift(cloneModel(model));
    model = historyFuture.shift();
    updateScope(rootScope, oldModel, model);
    for (const cb of afterUpdateCallbacks) cb(oldModel, model);
    updateSubscriptions();
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
    container.innerHTML = '';
    afterUpdateCallbacks.length = 0;

    // Reset root scope — clear all old properties first
    for (const key of Object.keys(rootScope)) delete rootScope[key];
    Object.assign(rootScope, createScope(null));

    // Re-render with new template, preserving model
    template = newTemplate;
    const dom = renderNode(template);
    if (dom) container.appendChild(dom);

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
      if (currentSubscription) {
        unsubscribe(currentSubscription);
      }
      if (bigLensWs) {
        bigLensWs.close();
      }
      if (updateWorker) {
        updateWorker.terminate();
        updateWorker = null;
      }
      destroyScope(rootScope);
      container.innerHTML = '';
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
