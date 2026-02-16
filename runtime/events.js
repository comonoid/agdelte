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

import { formatWorkerError, getPool } from './worker-pool.js';
import { subscribeLegacy } from './legacy-events.js';

// WebSocket connections pool (shared with commands)
export const wsConnections = new Map();

// Worker channel connections (shared with commands for channelSend)
export const channelConnections = new Map();

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

    // onKeys: key-to-message mapping with P0 (immediate) dispatch
    onKeys: (pairs) => {
      const pairArray = agdaListToArray(pairs);
      const keyMap = new Map();
      for (const pair of pairArray) {
        // Agda pair (_,_) can be:
        //   Function format: (cb) => cb["_,_"](key, msg)
        //   Object format:   {"_,_": cb => cb["_,_"](key, msg)}
        let k, m;
        try {
          if (typeof pair === 'function') {
            pair({ '_,_': (a, b) => { k = a; m = b; } });
          } else if (pair && typeof pair['_,_'] === 'function') {
            pair['_,_']({ '_,_': (a, b) => { k = a; m = b; } });
          }
        } catch { /* ignore extraction failure */ }
        if (k !== undefined) keyMap.set(k, m);
      }
      const listener = (e) => {
        const msg = keyMap.get(e.key);
        if (msg !== undefined) dispatchImmediate(msg);
      };
      document.addEventListener('keydown', listener);
      return { unsubscribe: () => document.removeEventListener('keydown', listener) };
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
          if (completed) return;
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
          completed = true;
          controller.abort();
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
          if (completed) return;
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
          completed = true;
          controller.abort();
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

      // Wrap all dispatcher channels through debouncedDispatch
      const wrappedDispatchers = {
        immediate: debouncedDispatch,
        normal: debouncedDispatch,
        background: debouncedDispatch
      };
      const sub = interpretEvent(innerEvent, debouncedDispatch, wrappedDispatchers);
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

      // Wrap all dispatcher channels through throttledDispatch
      const wrappedDispatchers = {
        immediate: throttledDispatch,
        normal: throttledDispatch,
        background: throttledDispatch
      };
      const sub = interpretEvent(innerEvent, throttledDispatch, wrappedDispatchers);
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

      // Close old WS: close first, then replace handlers with no-ops
      // to avoid message loss window between nulling handlers and closing
      const oldWs = wsConnections.get(url);
      if (oldWs) {
        if (oldWs.readyState === WebSocket.OPEN || oldWs.readyState === WebSocket.CONNECTING) {
          oldWs.close();
        }
        const noop = () => {};
        oldWs.onopen = noop;
        oldWs.onmessage = noop;
        oldWs.onclose = noop;
        oldWs.onerror = noop;
      }
      // Register for wsSend (overwrites previous - last connection wins)
      wsConnections.set(url, ws);

      return {
        unsubscribe: () => {
          // Clean up only if this is still the active connection
          if (wsConnections.get(url) === ws) {
            wsConnections.delete(url);
          }
          ws.onopen = null;
          ws.onmessage = null;
          ws.onclose = null;
          ws.onerror = null;
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
      const makeFoldDispatch = (priorityDispatch) => (inputVal) => {
        state = step(inputVal)(state);
        priorityDispatch(state);
      };
      const wrappedDispatchers = {
        immediate: makeFoldDispatch(dispatchImmediate),
        normal: makeFoldDispatch(dispatchNormal),
        background: makeFoldDispatch(dispatchBackground)
      };
      const sub = interpretEvent(innerEvent, makeFoldDispatch(dispatchNormal), wrappedDispatchers);
      return {
        unsubscribe: () => sub.unsubscribe()
      };
    },

    // mapFilterE: map + filter via Maybe (uses inner event's priority)
    // Scott: mapFilterE(_typeB, f, innerEvent)
    mapFilterE: (_typeB, f, innerEvent) => {
      const makeFilterDispatch = (priorityDispatch) => (inputVal) => {
        const maybeResult = f(inputVal);
        // Extract Maybe: just(x) → dispatch(x), nothing → skip
        // Use explicit null/undefined check instead of truthy
        if (maybeResult !== null && maybeResult !== undefined) {
          let isJust = false;
          let result;
          maybeResult({
            just: (x) => { isJust = true; result = x; },
            nothing: () => {}
          });
          if (isJust) priorityDispatch(result);
        }
      };
      const wrappedDispatchers = {
        immediate: makeFilterDispatch(dispatchImmediate),
        normal: makeFilterDispatch(dispatchNormal),
        background: makeFilterDispatch(dispatchBackground)
      };
      const sub = interpretEvent(innerEvent, makeFilterDispatch(dispatchNormal), wrappedDispatchers);
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

      // Route all meta-event channels through metaDispatch
      const metaDispatchers = {
        immediate: metaDispatch,
        normal: metaDispatch,
        background: metaDispatch
      };
      const metaSub = interpretEvent(metaEvent, metaDispatch, metaDispatchers);

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

      let terminated = false;

      w.onmessage = (e) => {
        if (terminated) return;
        dispatchBackground(onResult(typeof e.data === 'string' ? e.data : JSON.stringify(e.data)));
      };

      w.onerror = (e) => {
        if (terminated) return;
        dispatchBackground(onError(formatWorkerError(e)));
      };

      // Send input to worker
      w.postMessage(input);

      return {
        unsubscribe: () => {
          terminated = true;
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

      let terminated = false;

      w.onmessage = (e) => {
        if (terminated) return;
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
        if (terminated) return;
        dispatchBackground(onError(formatWorkerError(e)));
      };

      w.postMessage(input);

      return {
        unsubscribe: () => {
          terminated = true;
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

    // race: subscribe to all events in list, first to fire wins
    // All participants dispatch at normal priority so the race is fair —
    // otherwise P1 events (timeout) always beat P2 events (httpGet)
    // regardless of which actually fires first.
    race: (eventList) => {
      const events = agdaListToArray(eventList);
      if (events.length === 0) {
        return { unsubscribe: () => {} };
      }

      let finished = false;
      const subs = [];

      const raceDispatch = (val) => {
        if (finished) return;
        finished = true;
        dispatchNormal(val);
        subs.forEach(s => s.unsubscribe());
      };

      events.forEach((evt) => {
        const wrappedDispatchers = {
          immediate: raceDispatch,
          normal: raceDispatch,
          background: raceDispatch
        };
        const sub = interpretEvent(evt, raceDispatch, wrappedDispatchers);
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
    // Scott: allocShared(numBytes, handler) or allocShared(numBytes, handler, onError)
    // NOTE: Requires Cross-Origin-Opener-Policy and Cross-Origin-Embedder-Policy headers
    allocShared: (numBytes, handler, onError) => {
      const n = typeof numBytes === 'bigint' ? Number(numBytes) : numBytes;
      try {
        const buffer = new SharedArrayBuffer(n);
        dispatchNormal(handler(buffer));
      } catch (e) {
        console.error('allocShared failed (COOP/COEP headers required):', e.message);
        if (onError) {
          dispatchNormal(onError(e.message));
        }
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

      let terminated = false;

      w.onmessage = (e) => {
        if (terminated) return;
        dispatchBackground(onResult(typeof e.data === 'string' ? e.data : JSON.stringify(e.data)));
      };

      w.onerror = (e) => {
        if (terminated) return;
        dispatchBackground(onError(formatWorkerError(e)));
      };

      // Send input + shared buffer to worker
      w.postMessage({ input, buffer }, []);

      return {
        unsubscribe: () => {
          terminated = true;
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

      let terminated = false;

      w.onmessage = (e) => {
        if (terminated) return;
        dispatchBackground(onMessage(typeof e.data === 'string' ? e.data : JSON.stringify(e.data)));
      };

      w.onerror = (e) => {
        if (terminated) return;
        dispatchBackground(onError(formatWorkerError(e)));
      };

      // Register for channelSend
      channelConnections.set(scriptUrl, w);

      return {
        unsubscribe: () => {
          terminated = true;
          channelConnections.delete(scriptUrl);
          w.terminate();
        }
      };
    },

    // onUrlChange: URL change (popstate/hashchange) (P1 - normal, user navigation)
    // Uses hash-based routing (#/path) so apps work when served from any URL
    onUrlChange: (handler) => {
      const getRoutePath = () => {
        const hash = window.location.hash;
        return hash ? hash.slice(1) : '/';
      };

      const listener = () => {
        dispatchNormal(handler(getRoutePath()));
      };

      window.addEventListener('popstate', listener);
      window.addEventListener('hashchange', listener);

      // Dispatch initial URL only on first subscribe (not re-subscribes)
      if (!interpretEvent._urlInitialized) {
        interpretEvent._urlInitialized = true;
        dispatchNormal(handler(getRoutePath()));
      }

      return {
        unsubscribe: () => {
          window.removeEventListener('popstate', listener);
          window.removeEventListener('hashchange', listener);
        }
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
        dispatchNormal(handler(String(timestamp)));
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

      // Guard against NaN/Infinity parameters
      if (!isFinite(pos) || !isFinite(vel) || !isFinite(tgt) ||
          !isFinite(stiff) || !isFinite(damp)) {
        console.warn('springLoop: invalid parameters (NaN/Infinity), settling immediately');
        queueMicrotask(() => dispatchNormal(onSettled));
        return { unsubscribe: () => {} };
      }
      // Clamp stiffness/damping to non-negative values
      if (stiff < 0 || damp < 0) {
        console.warn('springLoop: negative stiffness/damping clamped to 0');
      }
      const stiffClamped = Math.max(0, stiff);
      const dampClamped = Math.max(0, damp);

      // Zero stiffness and zero damping means no restoring force — settle immediately
      if (stiffClamped === 0 && dampClamped === 0) {
        queueMicrotask(() => dispatchNormal(onSettled));
        return { unsubscribe: () => {} };
      }

      const tick = (dt) => {
        const dtSec = dt / 1000;
        const force = stiffClamped * (tgt - pos) - dampClamped * vel;
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
          requestAnimationFrame(loop);  // skip first frame (dt=0)
          return;
        }
        const dt = Math.min(timestamp - lastTime, 64); // cap to avoid spiral of death
        lastTime = timestamp;

        // Skip frame if dt is 0 (identical timestamps)
        if (dt <= 0) { requestAnimationFrame(loop); return; }

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
  const MAX_LIST_ITERATIONS = 100000;
  const arr = [];
  let current = list;
  let iterations = 0;
  while (current) {
    if (++iterations > MAX_LIST_ITERATIONS) {
      console.warn('agdaListToArray: exceeded max iterations, possible infinite list');
      break;
    }
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
 * Creates KeyboardEvent record for Agda (Scott-encoded, object format)
 * Compiled Agda accesses fields via: a["mkKeyboardEvent"]({"mkKeyboardEvent": (k,c,...) => k})
 * So the record must be: {"mkKeyboardEvent": cb => cb["mkKeyboardEvent"](fields...)}
 */
function mkKeyboardEvent(e) {
  return {"mkKeyboardEvent": (cb) => cb["mkKeyboardEvent"](
    e.key,
    e.code,
    e.ctrlKey,
    e.altKey,
    e.shiftKey,
    e.metaKey,
    e.repeat,
    BigInt(e.location)
  )};
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
