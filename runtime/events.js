/**
 * Agdelte Runtime - Event Interpreter
 *
 * Event is now a data type (AST), not Signal.
 * Runtime interprets this AST and creates subscriptions.
 *
 * Scott encoding:
 *   Event.never     = cb => cb.never()
 *   Event.interval  = ms => msg => cb => cb.interval(ms, msg)
 *   Event.merge     = e1 => e2 => cb => cb.merge(e1, e2)
 */

// WebSocket connections pool (shared with commands)
export const wsConnections = new Map();

// Helper: format worker error with details (filename, line, stack)
function formatWorkerError(e) {
  const parts = [e.message || 'Worker error'];
  if (e.filename) parts.push(`at ${e.filename}:${e.lineno || '?'}:${e.colno || '?'}`);
  if (e.error?.stack) parts.push(`\nStack: ${e.error.stack}`);
  return parts.join(' ');
}

// Worker channel connections (shared with commands for channelSend)
export const channelConnections = new Map();

// ─── Worker Pool ────────────────────────────────────────────────────
const POOL_IDLE_TIMEOUT = 30000; // 30s without tasks → cleanup
const POOL_CHECK_INTERVAL = 5000;

/**
 * Manages a pool of Web Workers for parallel task execution.
 *
 * Features:
 * - Reuses workers to avoid creation overhead
 * - Queues tasks when all workers busy
 * - Auto-cleanup after idle timeout (30s)
 * - Cancellable tasks
 *
 * @example
 * const pool = new WorkerPool(4, '/workers/compute.js');
 * const handle = pool.submit(inputData, onResult, onError);
 * handle.cancel(); // Cancel if needed
 */
class WorkerPool {
  /**
   * @param {number} maxSize - Maximum concurrent workers
   * @param {string} scriptUrl - Worker script URL
   */
  constructor(maxSize, scriptUrl) {
    this.maxSize = maxSize;
    this.scriptUrl = scriptUrl;
    this.idle = [];      // idle Worker instances
    this.active = 0;     // count of active tasks
    this.queue = [];     // pending tasks: { input, onMessage, onError, resolve }
    this.lastUsed = Date.now();
    this._cleanupTimer = setInterval(() => this._cleanup(), POOL_CHECK_INTERVAL);
  }

  /**
   * Submit a task to the pool.
   * @param {*} input - Data to send to worker via postMessage
   * @param {Function} onMessage - Called with MessageEvent on worker response
   * @param {Function} onError - Called with error string on failure
   * @returns {{ cancel: Function }} Handle with cancel() method
   */
  submit(input, onMessage, onError) {
    this.lastUsed = Date.now();
    let cancelled = false;
    let activeWorker = null;

    const task = { input, onMessage, onError, cancelled: false };

    const tryRun = () => {
      if (task.cancelled) return;
      if (this.idle.length > 0) {
        activeWorker = this.idle.pop();
      } else if (this.active + this.idle.length < this.maxSize) {
        try {
          activeWorker = new Worker(this.scriptUrl, { type: 'module' });
        } catch (e) {
          onError(e.message || 'Failed to create worker');
          return;
        }
      } else {
        // All busy — enqueue
        this.queue.push({ task, tryRun });
        return;
      }

      this.active++;
      activeWorker.onmessage = (e) => {
        if (task.cancelled) return;
        onMessage(e);
        this.active--;
        this._returnWorker(activeWorker);
        this._processQueue();
      };
      activeWorker.onerror = (e) => {
        if (task.cancelled) return;
        onError(formatWorkerError(e));
        this.active--;
        // Don't reuse errored worker — create fresh
        try { activeWorker.terminate(); } catch(_) {}
        this._processQueue();
      };
      activeWorker.postMessage(input);
    };

    tryRun();

    return {
      cancel: () => {
        task.cancelled = true;
        cancelled = true;
        if (activeWorker) {
          this.active--;
          // Terminate and don't return to pool (task was mid-flight)
          try { activeWorker.terminate(); } catch(_) {}
          this._processQueue();
        }
        // Remove from queue if still there
        this.queue = this.queue.filter(q => q.task !== task);
      }
    };
  }

  _returnWorker(w) {
    // Reset handlers before returning to pool
    w.onmessage = null;
    w.onerror = null;
    this.idle.push(w);
    this.lastUsed = Date.now();
  }

  _processQueue() {
    while (this.queue.length > 0 && (this.idle.length > 0 || this.active + this.idle.length < this.maxSize)) {
      const next = this.queue.shift();
      if (!next.task.cancelled) {
        next.tryRun();
        break;
      }
    }
  }

  _cleanup() {
    if (this.active === 0 && this.queue.length === 0 &&
        Date.now() - this.lastUsed > POOL_IDLE_TIMEOUT) {
      this.idle.forEach(w => w.terminate());
      this.idle = [];
      this._isEmpty = true;  // Mark for removal from registry
    }
  }

  destroy() {
    clearInterval(this._cleanupTimer);
    this.idle.forEach(w => w.terminate());
    this.idle = [];
    this.queue = [];
    this._isEmpty = true;
  }
}

// Global pool registry: key = "poolSize:scriptUrl"
const workerPools = new Map();

// Periodic cleanup of empty pools from registry
setInterval(() => {
  for (const [key, pool] of workerPools) {
    if (pool._isEmpty) {
      pool.destroy();
      workerPools.delete(key);
    }
  }
}, POOL_CHECK_INTERVAL * 2);

function getPool(poolSize, scriptUrl) {
  const poolSizeNum = typeof poolSize === 'bigint' ? Number(poolSize) : poolSize;
  const key = `${poolSizeNum}:${scriptUrl}`;
  if (!workerPools.has(key)) {
    workerPools.set(key, new WorkerPool(poolSizeNum, scriptUrl));
  }
  return workerPools.get(key);
}

/**
 * Creates WsMsg (Scott-encoded)
 */
function mkWsMsg(tag, value) {
  return (cb) => {
    switch (tag) {
      case 'WsConnected': return cb.WsConnected();
      case 'WsMessage': return cb.WsMessage(value);
      case 'WsClosed': return cb.WsClosed();
      case 'WsError': return cb.WsError(value);
    }
  };
}

/**
 * Interprets Event AST and creates subscriptions
 * @param {Object} event - Event (Scott-encoded)
 * @param {Function} dispatch - Message dispatcher (for backward compat, uses normal priority)
 * @param {Object} [dispatchers] - Optional priority dispatchers { immediate, normal, background }
 * @returns {Object} - { unsubscribe: () => void }
 */
export function interpretEvent(event, dispatch, dispatchers = null) {
  if (!event) {
    return { unsubscribe: () => {} };
  }

  // Priority dispatchers: use provided or fall back to single dispatch
  const dispatchImmediate = dispatchers?.immediate || dispatch;
  const dispatchNormal = dispatchers?.normal || dispatch;
  const dispatchBackground = dispatchers?.background || dispatch;

  // Scott encoding: call event with handler object
  return event({
    // never: do nothing
    never: () => ({ unsubscribe: () => {} }),

    // interval: periodic event (P2 - background)
    interval: (ms, msg) => {
      const msNum = typeof ms === 'bigint' ? Number(ms) : ms;
      const id = setInterval(() => dispatchBackground(msg), msNum);
      return { unsubscribe: () => clearInterval(id) };
    },

    // timeout: one-shot event (P1 - normal)
    timeout: (ms, msg) => {
      const msNum = typeof ms === 'bigint' ? Number(ms) : ms;
      const id = setTimeout(() => dispatchNormal(msg), msNum);
      return { unsubscribe: () => clearTimeout(id) };
    },

    // onKeyDown: keyboard (keydown) - P0 (immediate)
    onKeyDown: (handler) => {
      const listener = (e) => {
        const keyEvent = mkKeyboardEvent(e);
        const maybeMsg = handler(keyEvent);
        const msg = extractMaybe(maybeMsg);
        if (msg !== null) {
          dispatchImmediate(msg);
        }
      };
      document.addEventListener('keydown', listener);
      return { unsubscribe: () => document.removeEventListener('keydown', listener) };
    },

    // onKeyUp: keyboard (keyup) - P0 (immediate)
    onKeyUp: (handler) => {
      const listener = (e) => {
        const keyEvent = mkKeyboardEvent(e);
        const maybeMsg = handler(keyEvent);
        const msg = extractMaybe(maybeMsg);
        if (msg !== null) {
          dispatchImmediate(msg);
        }
      };
      document.addEventListener('keyup', listener);
      return { unsubscribe: () => document.removeEventListener('keyup', listener) };
    },

    // httpGet: HTTP GET request - P2 (background)
    httpGet: (url, onSuccess, onError) => {
      const controller = new AbortController();
      let completed = false;

      fetch(url, { signal: controller.signal })
        .then(async (response) => {
          if (completed) return;
          if (!response.ok) {
            throw new Error(`HTTP ${response.status}: ${response.statusText}`);
          }
          const text = await response.text();
          completed = true;
          dispatchBackground(onSuccess(text));
        })
        .catch((error) => {
          if (completed || error.name === 'AbortError') return;
          completed = true;
          dispatchBackground(onError(error.message));
        });

      return {
        unsubscribe: () => {
          if (!completed) controller.abort();
        }
      };
    },

    // httpPost: HTTP POST request - P2 (background)
    httpPost: (url, body, onSuccess, onError) => {
      const controller = new AbortController();
      let completed = false;

      fetch(url, {
        method: 'POST',
        headers: { 'Content-Type': 'text/plain' },
        body,
        signal: controller.signal
      })
        .then(async (response) => {
          if (completed) return;
          if (!response.ok) {
            throw new Error(`HTTP ${response.status}: ${response.statusText}`);
          }
          const text = await response.text();
          completed = true;
          dispatchBackground(onSuccess(text));
        })
        .catch((error) => {
          if (completed || error.name === 'AbortError') return;
          completed = true;
          dispatchBackground(onError(error.message));
        });

      return {
        unsubscribe: () => {
          if (!completed) controller.abort();
        }
      };
    },

    // merge: combine two events
    merge: (e1, e2) => {
      const sub1 = interpretEvent(e1, dispatch, dispatchers);
      const sub2 = interpretEvent(e2, dispatch, dispatchers);
      return {
        unsubscribe: () => {
          sub1.unsubscribe();
          sub2.unsubscribe();
        }
      };
    },

    // debounce: delay after pause (P1 - normal)
    debounce: (ms, innerEvent) => {
      const msNum = typeof ms === 'bigint' ? Number(ms) : ms;
      let timeoutId = null;
      let lastMsg = null;

      const debouncedDispatch = (msg) => {
        lastMsg = msg;
        if (timeoutId) clearTimeout(timeoutId);
        timeoutId = setTimeout(() => {
          dispatchNormal(lastMsg);
          timeoutId = null;
        }, msNum);
      };

      const sub = interpretEvent(innerEvent, debouncedDispatch, dispatchers);
      return {
        unsubscribe: () => {
          if (timeoutId) clearTimeout(timeoutId);
          sub.unsubscribe();
        }
      };
    },

    // throttle: rate limiting (P1 - normal)
    throttle: (ms, innerEvent) => {
      const msNum = typeof ms === 'bigint' ? Number(ms) : ms;
      let lastCall = 0;
      let timeoutId = null;
      let pendingMsg = null;

      const throttledDispatch = (msg) => {
        const now = Date.now();
        const remaining = msNum - (now - lastCall);

        if (remaining <= 0) {
          if (timeoutId) {
            clearTimeout(timeoutId);
            timeoutId = null;
          }
          lastCall = now;
          dispatchNormal(msg);
        } else {
          pendingMsg = msg;
          if (!timeoutId) {
            timeoutId = setTimeout(() => {
              lastCall = Date.now();
              timeoutId = null;
              if (pendingMsg !== null) {
                dispatchNormal(pendingMsg);
                pendingMsg = null;
              }
            }, remaining);
          }
        }
      };

      const sub = interpretEvent(innerEvent, throttledDispatch, dispatchers);
      return {
        unsubscribe: () => {
          if (timeoutId) clearTimeout(timeoutId);
          sub.unsubscribe();
        }
      };
    },

    // wsConnect: WebSocket connection (P2 - background for data, P1 for connection events)
    // Note: Multiple connections to same URL are supported via wsConnections Map
    // wsSend uses the most recent connection for each URL
    wsConnect: (url, handler) => {
      const ws = new WebSocket(url);

      ws.onopen = () => {
        dispatchNormal(handler(mkWsMsg('WsConnected')));
      };

      ws.onmessage = (e) => {
        dispatchBackground(handler(mkWsMsg('WsMessage', e.data)));
      };

      ws.onerror = (e) => {
        // WebSocket error events are Event objects, not Error objects
        // They don't have a .message property - extract what info we can
        const errorMsg = e.error?.message ||
                        (ws.readyState === WebSocket.CLOSED ? 'Connection failed' : 'WebSocket error');
        dispatchNormal(handler(mkWsMsg('WsError', errorMsg)));
      };

      ws.onclose = () => {
        dispatchNormal(handler(mkWsMsg('WsClosed')));
        // Clean up only if this is still the active connection
        if (wsConnections.get(url) === ws) {
          wsConnections.delete(url);
        }
      };

      // Register for wsSend (overwrites previous - last connection wins)
      wsConnections.set(url, ws);

      return {
        unsubscribe: () => {
          // Clean up only if this is still the active connection
          if (wsConnections.get(url) === ws) {
            wsConnections.delete(url);
          }
          ws.onerror = null;  // Prevent stale error handler
          if (ws.readyState === WebSocket.OPEN || ws.readyState === WebSocket.CONNECTING) {
            ws.close();
          }
        }
      };
    },

    // foldE: accumulate state across event occurrences (uses inner event's priority)
    // Scott: foldE(_typeB, init, step, innerEvent)
    foldE: (_typeB, init, step, innerEvent) => {
      let state = init;
      const wrappedDispatch = (inputVal) => {
        state = step(inputVal)(state);
        dispatchNormal(state);
      };
      // All priorities route through wrappedDispatch to maintain the fold chain
      const wrappedDispatchers = {
        immediate: wrappedDispatch,
        normal: wrappedDispatch,
        background: wrappedDispatch
      };
      const sub = interpretEvent(innerEvent, wrappedDispatch, wrappedDispatchers);
      return {
        unsubscribe: () => sub.unsubscribe()
      };
    },

    // mapFilterE: map + filter via Maybe (uses inner event's priority)
    // Scott: mapFilterE(_typeB, f, innerEvent)
    mapFilterE: (_typeB, f, innerEvent) => {
      const wrappedDispatch = (inputVal) => {
        const maybeResult = f(inputVal);
        // Extract Maybe: just(x) → dispatch(x), nothing → skip
        if (maybeResult) {
          const result = maybeResult({
            just: (x) => x,
            nothing: () => null
          });
          if (result !== null) dispatchNormal(result);
        }
      };
      // All priorities route through wrappedDispatch to maintain the filter chain
      const wrappedDispatchers = {
        immediate: wrappedDispatch,
        normal: wrappedDispatch,
        background: wrappedDispatch
      };
      const sub = interpretEvent(innerEvent, wrappedDispatch, wrappedDispatchers);
      return {
        unsubscribe: () => sub.unsubscribe()
      };
    },

    // switchE: start with initial event, switch on meta-event
    // Scott: switchE(initialEvent, metaEvent)
    switchE: (initialEvent, metaEvent) => {
      let currentSub = interpretEvent(initialEvent, dispatch, dispatchers);

      const metaDispatch = (newEvent) => {
        // Unsubscribe from current, switch to new
        currentSub.unsubscribe();
        currentSub = interpretEvent(newEvent, dispatch, dispatchers);
      };

      const metaSub = interpretEvent(metaEvent, metaDispatch, dispatchers);

      return {
        unsubscribe: () => {
          currentSub.unsubscribe();
          metaSub.unsubscribe();
        }
      };
    },

    // worker: Web Worker (P2 - background for results)
    worker: (scriptUrl, input, onResult, onError) => {
      let w;
      try {
        w = new Worker(scriptUrl, { type: 'module' });
      } catch (e) {
        dispatchBackground(onError(e.message || 'Failed to create worker'));
        return { unsubscribe: () => {} };
      }

      w.onmessage = (e) => {
        dispatchBackground(onResult(typeof e.data === 'string' ? e.data : JSON.stringify(e.data)));
      };

      w.onerror = (e) => {
        dispatchBackground(onError(formatWorkerError(e)));
      };

      // Send input to worker
      w.postMessage(input);

      return {
        unsubscribe: () => {
          w.terminate();
        }
      };
    },

    // workerWithProgress: worker that sends progress, result, and error events (P2 - background)
    workerWithProgress: (scriptUrl, input, onProgress, onResult, onError) => {
      let w;
      try {
        w = new Worker(scriptUrl, { type: 'module' });
      } catch (e) {
        dispatchBackground(onError(e.message || 'Failed to create worker'));
        return { unsubscribe: () => {} };
      }

      w.onmessage = (e) => {
        const data = e.data;
        if (data && typeof data === 'object') {
          if (data.type === 'progress') {
            dispatchBackground(onProgress(String(data.value)));
          } else if (data.type === 'done') {
            dispatchBackground(onResult(typeof data.result === 'string' ? data.result : JSON.stringify(data.result)));
          } else if (data.type === 'error') {
            dispatchBackground(onError(data.message || 'Worker error'));
          } else {
            // Default: treat as result
            dispatchBackground(onResult(JSON.stringify(data)));
          }
        } else {
          dispatchBackground(onResult(typeof data === 'string' ? data : JSON.stringify(data)));
        }
      };

      w.onerror = (e) => {
        dispatchBackground(onError(formatWorkerError(e)));
      };

      w.postMessage(input);

      return {
        unsubscribe: () => {
          w.terminate();
        }
      };
    },

    // parallel: subscribe to all events in list, collect first result from each (P2 - background)
    // Scott: parallel(_typeB, eventList, mapFn)
    parallel: (_typeB, eventList, mapFn) => {
      const events = agdaListToArray(eventList);
      const total = events.length;
      if (total === 0) {
        // Empty list: dispatch mapped empty list immediately
        dispatchBackground(mapFn(mkAgdaList([])));
        return { unsubscribe: () => {} };
      }

      const results = new Array(total);
      const done = new Array(total).fill(false);
      let remaining = total;
      let finished = false;
      const subs = [];

      events.forEach((evt, i) => {
        // Create wrapped dispatch that collects results
        const wrappedDispatch = (val) => {
          if (finished || done[i]) return;
          results[i] = val;
          done[i] = true;
          remaining--;
          if (remaining === 0) {
            finished = true;
            dispatchBackground(mapFn(mkAgdaList(results)));
            // Unsubscribe all after completion
            subs.forEach(s => s.unsubscribe());
          }
        };
        // All priorities route through wrappedDispatch
        const wrappedDispatchers = {
          immediate: wrappedDispatch,
          normal: wrappedDispatch,
          background: wrappedDispatch
        };
        const sub = interpretEvent(evt, wrappedDispatch, wrappedDispatchers);
        subs.push(sub);
      });

      return {
        unsubscribe: () => {
          finished = true;
          subs.forEach(s => s.unsubscribe());
        }
      };
    },

    // race: subscribe to all events in list, first to fire wins (uses inner event's priority)
    race: (eventList) => {
      const events = agdaListToArray(eventList);
      if (events.length === 0) {
        return { unsubscribe: () => {} };
      }

      let finished = false;
      const subs = [];

      events.forEach((evt) => {
        // Create wrapped dispatch that handles race semantics
        const wrappedDispatch = (val) => {
          if (finished) return;
          finished = true;
          dispatchNormal(val);
          // Unsubscribe all (including self)
          subs.forEach(s => s.unsubscribe());
        };
        // All priorities route through wrappedDispatch
        const wrappedDispatchers = {
          immediate: wrappedDispatch,
          normal: wrappedDispatch,
          background: wrappedDispatch
        };
        const sub = interpretEvent(evt, wrappedDispatch, wrappedDispatchers);
        subs.push(sub);
      });

      return {
        unsubscribe: () => {
          finished = true;
          subs.forEach(s => s.unsubscribe());
        }
      };
    },

    // poolWorker: worker from pool (one-shot task) (P2 - background)
    // Scott: poolWorker(poolSize, scriptUrl, input, onResult, onError)
    poolWorker: (poolSize, scriptUrl, input, onResult, onError) => {
      const pool = getPool(poolSize, scriptUrl);
      const handle = pool.submit(
        input,
        (e) => {
          dispatchBackground(onResult(typeof e.data === 'string' ? e.data : JSON.stringify(e.data)));
        },
        (errMsg) => {
          dispatchBackground(onError(errMsg));
        }
      );
      return { unsubscribe: () => handle.cancel() };
    },

    // poolWorkerWithProgress: pool worker with progress protocol (P2 - background)
    // Scott: poolWorkerWithProgress(poolSize, scriptUrl, input, onProgress, onResult, onError)
    poolWorkerWithProgress: (poolSize, scriptUrl, input, onProgress, onResult, onError) => {
      const pool = getPool(poolSize, scriptUrl);
      const handle = pool.submit(
        input,
        (e) => {
          const data = e.data;
          if (data && typeof data === 'object') {
            if (data.type === 'progress') {
              dispatchBackground(onProgress(String(data.value)));
            } else if (data.type === 'done') {
              dispatchBackground(onResult(typeof data.result === 'string' ? data.result : JSON.stringify(data.result)));
            } else if (data.type === 'error') {
              dispatchBackground(onError(data.message || 'Worker error'));
            } else {
              dispatchBackground(onResult(JSON.stringify(data)));
            }
          } else {
            dispatchBackground(onResult(typeof data === 'string' ? data : JSON.stringify(data)));
          }
        },
        (errMsg) => {
          dispatchBackground(onError(errMsg));
        }
      );
      return { unsubscribe: () => handle.cancel() };
    },

    // allocShared: allocate SharedArrayBuffer (P1 - normal, synchronous operation)
    // Scott: allocShared(numBytes, handler)
    // NOTE: Requires COOP/COEP headers. See doc/KNOWN_ISSUES.md
    allocShared: (numBytes, handler) => {
      const n = typeof numBytes === 'bigint' ? Number(numBytes) : numBytes;
      try {
        const buffer = new SharedArrayBuffer(n);
        dispatchNormal(handler(buffer));
      } catch (e) {
        console.error('allocShared failed (COOP/COEP headers required):', e.message);
      }
      return { unsubscribe: () => {} };
    },

    // workerShared: worker with SharedArrayBuffer access (P2 - background)
    // Scott: workerShared(buffer, scriptUrl, input, onResult, onError)
    workerShared: (buffer, scriptUrl, input, onResult, onError) => {
      let w;
      try {
        w = new Worker(scriptUrl, { type: 'module' });
      } catch (e) {
        dispatchBackground(onError(e.message || 'Failed to create worker'));
        return { unsubscribe: () => {} };
      }

      w.onmessage = (e) => {
        dispatchBackground(onResult(typeof e.data === 'string' ? e.data : JSON.stringify(e.data)));
      };

      w.onerror = (e) => {
        dispatchBackground(onError(formatWorkerError(e)));
      };

      // Send input + shared buffer to worker
      w.postMessage({ input, buffer }, []);

      return {
        unsubscribe: () => {
          w.terminate();
        }
      };
    },

    // workerChannel: long-lived bidirectional worker connection (P2 - background)
    // Scott: workerChannel(scriptUrl, onMessage, onError)
    workerChannel: (scriptUrl, onMessage, onError) => {
      let w;
      try {
        w = new Worker(scriptUrl, { type: 'module' });
      } catch (e) {
        dispatchBackground(onError(e.message || 'Failed to create worker'));
        return { unsubscribe: () => {} };
      }

      w.onmessage = (e) => {
        dispatchBackground(onMessage(typeof e.data === 'string' ? e.data : JSON.stringify(e.data)));
      };

      w.onerror = (e) => {
        dispatchBackground(onError(formatWorkerError(e)));
      };

      // Register for channelSend
      channelConnections.set(scriptUrl, w);

      return {
        unsubscribe: () => {
          channelConnections.delete(scriptUrl);
          w.terminate();
        }
      };
    },

    // onUrlChange: URL change (popstate) (P1 - normal, user navigation)
    onUrlChange: (handler) => {
      const listener = () => {
        dispatchNormal(handler(window.location.pathname + window.location.search));
      };

      window.addEventListener('popstate', listener);

      return {
        unsubscribe: () => window.removeEventListener('popstate', listener)
      };
    },

    // animationFrame: dispatch message on every animation frame (P1 - normal)
    animationFrame: (msg) => {
      let running = true;
      const loop = () => {
        if (!running) return;
        dispatchNormal(msg);
        requestAnimationFrame(loop);
      };
      requestAnimationFrame(loop);
      return {
        unsubscribe: () => { running = false; }
      };
    },

    // animationFrameWithTime: dispatch with timestamp (ms since origin) (P1 - normal)
    animationFrameWithTime: (handler) => {
      let running = true;
      const loop = (timestamp) => {
        if (!running) return;
        dispatchNormal(handler(timestamp));
        requestAnimationFrame(loop);
      };
      requestAnimationFrame(loop);
      return {
        unsubscribe: () => { running = false; }
      };
    },

    // springLoop: animated spring that ticks until settled (P1 - normal for ticks)
    // Scott: springLoop(position, velocity, target, stiffness, damping, onTick, onSettled)
    // onTick receives current position each frame
    // onSettled is dispatched when spring settles
    springLoop: (position, velocity, target, stiffness, damping, onTick, onSettled) => {
      let running = true;
      let lastTime = null;
      let pos = Number(position);
      let vel = Number(velocity);
      const tgt = Number(target);
      const stiff = Number(stiffness);
      const damp = Number(damping);

      const tick = (dt) => {
        const dtSec = dt / 1000;
        const force = stiff * (tgt - pos) - damp * vel;
        vel = vel + force * dtSec;
        pos = pos + vel * dtSec;
      };

      const isSettled = () => {
        return Math.abs(pos - tgt) < 0.01 && Math.abs(vel) < 0.01;
      };

      const loop = (timestamp) => {
        if (!running) return;
        if (lastTime === null) {
          lastTime = timestamp;
        }
        const dt = Math.min(timestamp - lastTime, 64); // cap to avoid spiral of death
        lastTime = timestamp;

        // Tick in 4ms steps for stability
        let remaining = dt;
        while (remaining >= 4) {
          tick(4);
          remaining -= 4;
        }
        if (remaining > 0) tick(remaining);

        dispatchNormal(onTick(pos));

        if (isSettled()) {
          running = false;
          dispatchNormal(onSettled);
        } else {
          requestAnimationFrame(loop);
        }
      };
      requestAnimationFrame(loop);
      return {
        unsubscribe: () => { running = false; }
      };
    }
  });
}

/**
 * Convert Agda List (Scott-encoded) to JS Array
 * [] = cb => cb['[]']()
 * x ∷ xs = cb => cb['_∷_'](x, xs)
 */
function agdaListToArray(list) {
  // Agda JS backend compiles List to native JS Array
  if (Array.isArray(list)) return list;
  // Fallback: Scott-encoded list
  const arr = [];
  let current = list;
  while (current) {
    const result = current({
      '[]': () => null,
      '_∷_': (head, tail) => ({ head, tail })
    });
    if (result === null) break;
    arr.push(result.head);
    current = result.tail;
  }
  return arr;
}

/**
 * Convert JS Array to Agda List (Scott-encoded)
 */
function mkAgdaList(arr) {
  // Agda JS backend uses native JS Arrays for List
  return Array.from(arr);
}

/**
 * Creates KeyboardEvent record for Agda (Scott-encoded)
 * Agda record = { constructorName: cb => cb.constructorName(fields...) }
 */
function mkKeyboardEvent(e) {
  return {
    mkKeyboardEvent: (cb) => cb.mkKeyboardEvent(
      e.key,
      e.code,
      e.ctrlKey,
      e.altKey,
      e.shiftKey,
      e.metaKey,
      e.repeat,
      e.location
    )
  };
}

/**
 * Extracts value from Maybe (Scott-encoded)
 * Maybe.just(x)  = cb => cb.just(x)
 * Maybe.nothing  = cb => cb.nothing()
 */
function extractMaybe(maybe) {
  if (!maybe) return null;
  return maybe({
    just: (x) => x,
    nothing: () => null
  });
}

/**
 * Legacy: event subscription (for compatibility)
 */
export function subscribe(eventSpec, dispatch) {
  // If old format (plain object), use old logic
  if (eventSpec && eventSpec.type) {
    return subscribeLegacy(eventSpec, dispatch);
  }
  // Otherwise interpret as Event AST
  return interpretEvent(eventSpec, dispatch);
}

/**
 * Legacy subscription for old format {type, config}
 */
function subscribeLegacy(eventSpec, dispatch) {
  const { type, config } = eventSpec;

  switch (type) {
    case 'never':
      return { unsubscribe: () => {} };

    case 'interval': {
      const msNum = typeof config.ms === 'bigint' ? Number(config.ms) : config.ms;
      const id = setInterval(() => dispatch(config.msg), msNum);
      return { unsubscribe: () => clearInterval(id) };
    }

    case 'timeout': {
      const msNum = typeof config.ms === 'bigint' ? Number(config.ms) : config.ms;
      const id = setTimeout(() => dispatch(config.msg), msNum);
      return { unsubscribe: () => clearTimeout(id) };
    }

    case 'keyboard': {
      const listener = (e) => {
        const msg = config.handler({
          key: e.key,
          code: e.code,
          ctrl: e.ctrlKey,
          alt: e.altKey,
          shift: e.shiftKey,
          meta: e.metaKey
        });
        if (msg !== null && msg !== undefined) {
          dispatch(msg);
        }
      };
      document.addEventListener(config.eventType || 'keydown', listener);
      return {
        unsubscribe: () => document.removeEventListener(config.eventType || 'keydown', listener)
      };
    }

    case 'clipboardEvent': {
      const listener = (e) => {
        let data = '';
        if (config.event === 'paste') {
          data = (e.clipboardData || window.clipboardData)?.getData('text') || '';
        }
        const msg = config.handler(data);
        if (msg !== null && msg !== undefined) {
          dispatch(msg);
        }
      };
      document.addEventListener(config.event, listener);
      return {
        unsubscribe: () => document.removeEventListener(config.event, listener)
      };
    }

    default:
      console.warn(`Unknown event type: ${type}`);
      return { unsubscribe: () => {} };
  }
}

/**
 * Unsubscribe
 */
export function unsubscribe(subscription) {
  if (subscription && typeof subscription.unsubscribe === 'function') {
    subscription.unsubscribe();
  }
}

/**
 * Debounce/throttle utilities
 */
export function debounce(fn, ms) {
  let timeoutId;
  return (...args) => {
    clearTimeout(timeoutId);
    timeoutId = setTimeout(() => fn(...args), ms);
  };
}

export function throttle(fn, ms) {
  let lastCall = 0;
  let timeoutId;
  return (...args) => {
    const now = Date.now();
    const remaining = ms - (now - lastCall);
    if (remaining <= 0) {
      clearTimeout(timeoutId);
      lastCall = now;
      fn(...args);
    } else if (!timeoutId) {
      timeoutId = setTimeout(() => {
        lastCall = Date.now();
        timeoutId = null;
        fn(...args);
      }, remaining);
    }
  };
}
