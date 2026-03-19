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
import { listToArray, arrayToList, toBool, fromMaybe, ensureNumber, ensureString } from './agda-values.js';
import { bufferRegistry, mkBufferHandle } from './buffer-registry.js';

// --- Spring physics constants ---
const SPRING_POS_THRESHOLD_MIN = 0.01;
const SPRING_VEL_THRESHOLD_MIN = 0.01;
const SPRING_RANGE_SCALE = 0.001;
const SPRING_DT_CAP = 64;       // ms — cap per-frame dt to avoid spiral of death
const SPRING_TICK_STEP = 4;     // ms — fixed sub-step for integration

// WebSocket connections pool (shared with commands)
// Keyed by URL → Map of connectionId → WebSocket
export const wsConnections = new Map();
let _wsConnectionCounter = 0;

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
      case 'WsBinary': return cb.WsBinary(value);
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
  // Event is split into structural constructors (never, sub, merge, debounce,
  // throttle, foldE, mapFilterE, switchE, parallel, race) and leaf sources (Sub).
  // The `sub` handler delegates to interpretSub for leaf event sources.
  // Leaf handlers shared with interpretSub (backward compat for direct Scott-encoded values)
  const leafHandlers = makeLeafHandlers(dispatchImmediate, dispatchNormal, dispatchBackground);

  return event({
    // never: do nothing
    never: () => ({ unsubscribe: () => {} }),

    // sub: delegate to interpretSub for leaf event sources
    sub: (subEvent) => interpretSub(subEvent, dispatch, dispatchers),

    // Backward compat: spread all leaf handlers so old Event values
    // that directly use leaf constructors (without sub wrapper) still work.
    ...leafHandlers,

    // onKeys: key-to-message mapping with P0 (immediate) dispatch
    // (only in Event, not in Sub)
    onKeys: (pairs) => {
      const pairArray = listToArray(pairs).items;
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
      const ac = new AbortController();
      document.addEventListener('keydown', (e) => {
        const msg = keyMap.get(e.key);
        if (msg !== undefined) dispatchImmediate(msg);
      }, { signal: ac.signal });
      return { unsubscribe: () => ac.abort() };
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
    // Immediate-priority events bypass the debounce to preserve their semantics
    debounce: (ms, innerEvent) => {
      const msNum = ensureNumber(ms);
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

      const wrappedDispatchers = {
        immediate: dispatchImmediate,  // bypass debounce
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
    // Immediate-priority events bypass the throttle to preserve their semantics
    throttle: (ms, innerEvent) => {
      const msNum = ensureNumber(ms);
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

      const wrappedDispatchers = {
        immediate: dispatchImmediate,  // bypass throttle
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

    // foldE: accumulate state across event occurrences (uses inner event's priority)
    // Scott: foldE(_typeB, init, step, innerEvent)
    foldE: (_typeB, init, step, innerEvent) => {
      let state = init;
      // All priority channels funnel through a single state update to prevent
      // interleaving when a synchronous (P0) dispatch re-enters while a
      // background (P2) callback is pending.
      const updateAndDispatch = (priorityDispatch) => (inputVal) => {
        state = step(inputVal)(state);
        const snapshot = state;
        priorityDispatch(snapshot);
      };
      const wrappedDispatchers = {
        immediate: updateAndDispatch(dispatchImmediate),
        normal: updateAndDispatch(dispatchNormal),
        background: updateAndDispatch(dispatchBackground)
      };
      const sub = interpretEvent(innerEvent, updateAndDispatch(dispatchNormal), wrappedDispatchers);
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

    // parallel: subscribe to all events in list, collect first result from each (P2 - background)
    // Scott: parallel(_typeB, eventList, mapFn)
    parallel: (_typeB, eventList, mapFn) => {
      const events = listToArray(eventList).items;
      const total = events.length;
      if (total === 0) {
        // Empty list: dispatch mapped empty list immediately
        dispatchBackground(mapFn(arrayToList([])));
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
            dispatchBackground(mapFn(arrayToList(results)));
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

      // If synchronous events completed during the forEach loop, some
      // subscriptions may have been pushed after the completion unsubscribe.
      // Clean them up now.
      if (finished) {
        subs.forEach(s => s.unsubscribe());
      }

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
      const events = listToArray(eventList).items;
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

      for (const evt of events) {
        if (finished) break;  // winner already resolved, skip remaining
        const wrappedDispatchers = {
          immediate: raceDispatch,
          normal: raceDispatch,
          background: raceDispatch
        };
        const sub = interpretEvent(evt, raceDispatch, wrappedDispatchers);
        subs.push(sub);
      }

      // If a synchronous event won during the loop, some subscriptions
      // created before the winner may need cleanup (already handled by
      // raceDispatch), but the winner's own sub may have been pushed after
      // the completion unsubscribe. Clean up now.
      if (finished) {
        subs.forEach(s => s.unsubscribe());
      }

      return {
        unsubscribe: () => {
          finished = true;
          subs.forEach(s => s.unsubscribe());
        }
      };
    }
  });
}

/**
 * Build the leaf event handler map shared by interpretEvent (backward compat)
 * and interpretSub. Single source of truth — avoids handler duplication.
 */
function makeLeafHandlers(dispatchImmediate, dispatchNormal, dispatchBackground) {
  return {
    interval: (ms, msg) => {
      const msNum = ensureNumber(ms);
      const id = setInterval(() => dispatchBackground(msg), msNum);
      return { unsubscribe: () => clearInterval(id) };
    },
    timeout: (ms, msg) => {
      const msNum = ensureNumber(ms);
      const id = setTimeout(() => dispatchNormal(msg), msNum);
      return { unsubscribe: () => clearTimeout(id) };
    },
    animationFrame: (msg) => {
      let running = true;
      let rafId = 0;
      const loop = () => {
        if (!running) return;
        dispatchNormal(msg);
        if (running) rafId = requestAnimationFrame(loop);
      };
      rafId = requestAnimationFrame(loop);
      return { unsubscribe: () => { running = false; cancelAnimationFrame(rafId); } };
    },
    animationFrameWithTime: (handler) => {
      let running = true;
      let rafId = 0;
      const loop = (timestamp) => {
        if (!running) return;
        dispatchNormal(handler(timestamp));
        if (running) rafId = requestAnimationFrame(loop);
      };
      rafId = requestAnimationFrame(loop);
      return { unsubscribe: () => { running = false; cancelAnimationFrame(rafId); } };
    },
    springLoop: (cfg, onTick, onSettled) => {
      let position, velocity, target, stiffness, damping;
      cfg({ mkSpringConfig: (p, v, t, s, d) => { position = p; velocity = v; target = t; stiffness = s; damping = d; } });
      let running = true;
      let lastTime = null;
      let pos = ensureNumber(position);
      let vel = ensureNumber(velocity);
      const tgt = ensureNumber(target);
      const stiff = ensureNumber(stiffness);
      const damp = ensureNumber(damping);
      if (!isFinite(pos) || !isFinite(vel) || !isFinite(tgt) || !isFinite(stiff) || !isFinite(damp)) {
        console.warn('springLoop: invalid parameters (NaN/Infinity), settling immediately');
        queueMicrotask(() => dispatchNormal(onSettled));
        return { unsubscribe: () => {} };
      }
      if (stiff < 0 || damp < 0) console.warn('springLoop: negative stiffness/damping clamped to 0');
      const stiffClamped = Math.max(0, stiff);
      const dampClamped = Math.max(0, damp);
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
      const range = Math.abs(ensureNumber(position) - tgt);
      const posThreshold = Math.max(SPRING_POS_THRESHOLD_MIN, range * SPRING_RANGE_SCALE);
      const velThreshold = Math.max(SPRING_VEL_THRESHOLD_MIN, range * SPRING_RANGE_SCALE);
      const isSettled = () => Math.abs(pos - tgt) < posThreshold && Math.abs(vel) < velThreshold;
      let rafId = 0;
      const loop = (timestamp) => {
        if (!running) return;
        if (lastTime === null) { lastTime = timestamp; rafId = requestAnimationFrame(loop); return; }
        const dt = Math.min(timestamp - lastTime, SPRING_DT_CAP);
        lastTime = timestamp;
        if (dt <= 0) { rafId = requestAnimationFrame(loop); return; }
        let remaining = dt;
        while (remaining >= SPRING_TICK_STEP) { tick(SPRING_TICK_STEP); remaining -= SPRING_TICK_STEP; }
        if (remaining > 0) tick(remaining);
        dispatchNormal(onTick(pos));
        if (isSettled()) { running = false; dispatchNormal(onSettled); }
        else { rafId = requestAnimationFrame(loop); }
      };
      rafId = requestAnimationFrame(loop);
      return { unsubscribe: () => { running = false; cancelAnimationFrame(rafId); } };
    },
    // Global event listener factory: creates AbortController-managed listeners
    ...(() => {
      const mkGlobalListener = (eventName, mkEvent, dispatch) => (handler) => {
        const ac = new AbortController();
        document.addEventListener(eventName, (e) => {
          const msg = fromMaybe(handler(mkEvent(e)));
          if (msg !== null) dispatch(msg);
        }, { signal: ac.signal });
        return { unsubscribe: () => ac.abort() };
      };
      const keyImm   = (name) => mkGlobalListener(name, mkKeyboardEvent, dispatchImmediate);
      const mouseImm = (name) => mkGlobalListener(name, mkMouseEvent, dispatchImmediate);
      return {
        onKeyDown:   keyImm('keydown'),
        onKeyUp:     keyImm('keyup'),
        onMouseDown: mouseImm('mousedown'),
        onMouseUp:   mouseImm('mouseup'),
        onMouseMove: mkGlobalListener('mousemove', mkMouseEvent, dispatchNormal),
        onClick:     mouseImm('click'),
      };
    })(),
    // Shared HTTP fetch helper
    ...(() => {
      const httpFetch = (fetchOpts, onSuccess, onError) => {
        const controller = new AbortController();
        let completed = false;
        fetch(fetchOpts.url, { ...fetchOpts.init, signal: controller.signal })
          .then(async (response) => {
            if (completed) return;
            if (!response.ok) throw new Error(`HTTP ${response.status}: ${response.statusText}`);
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
        return { unsubscribe: () => { completed = true; controller.abort(); } };
      };
      return {
        httpGet: (url, onSuccess, onError) =>
          httpFetch({ url }, onSuccess, onError),
        httpPost: (url, body, onSuccess, onError) => {
          let contentType = 'text/plain';
          if (typeof body === 'string' && /^\s*[\[{]/.test(body)) {
            contentType = 'application/json';
          }
          return httpFetch(
            { url, init: { method: 'POST', headers: { 'Content-Type': contentType }, body } },
            onSuccess, onError
          );
        },
      };
    })(),
    wsConnect: (url, handler) => {
      let ws;
      try { ws = new WebSocket(url); }
      catch (e) {
        dispatchNormal(handler(mkWsMsg('WsError', e.message || 'Invalid WebSocket URL')));
        return { unsubscribe: () => {} };
      }
      const connId = ++_wsConnectionCounter;
      ws.onopen = () => dispatchNormal(handler(mkWsMsg('WsConnected')));
      ws.onmessage = (e) => {
        if (typeof e.data === 'string') {
          dispatchBackground(handler(mkWsMsg('WsMessage', e.data)));
        } else {
          // Binary frame (ArrayBuffer or Blob) — convert to base64 string
          const toBase64 = (ab) => {
            const bytes = new Uint8Array(ab);
            let binary = '';
            for (let i = 0; i < bytes.length; i++) binary += String.fromCharCode(bytes[i]);
            return btoa(binary);
          };
          if (e.data instanceof ArrayBuffer) {
            dispatchBackground(handler(mkWsMsg('WsBinary', toBase64(e.data))));
          } else if (e.data instanceof Blob) {
            e.data.arrayBuffer().then(ab => {
              dispatchBackground(handler(mkWsMsg('WsBinary', toBase64(ab))));
            });
          } else {
            dispatchBackground(handler(mkWsMsg('WsMessage', String(e.data))));
          }
        }
      };
      ws.onerror = (e) => {
        const errorMsg = e.error?.message || (ws.readyState === WebSocket.CLOSED ? 'Connection failed' : 'WebSocket error');
        dispatchNormal(handler(mkWsMsg('WsError', errorMsg)));
      };
      ws.onclose = () => {
        dispatchNormal(handler(mkWsMsg('WsClosed')));
        const urlConns = wsConnections.get(url);
        if (urlConns) { urlConns.delete(connId); if (urlConns.size === 0) wsConnections.delete(url); }
      };
      if (!wsConnections.has(url)) wsConnections.set(url, new Map());
      wsConnections.get(url).set(connId, ws);
      return {
        unsubscribe: () => {
          const urlConns = wsConnections.get(url);
          if (urlConns) { urlConns.delete(connId); if (urlConns.size === 0) wsConnections.delete(url); }
          ws.onopen = null; ws.onmessage = null; ws.onclose = null; ws.onerror = null;
          if (ws.readyState === WebSocket.OPEN || ws.readyState === WebSocket.CONNECTING) ws.close();
        }
      };
    },
    onUrlChange: (handler) => {
      const getRoutePath = () => { const hash = window.location.hash; return hash && hash.length > 1 ? hash.slice(1) : '/'; };
      let lastDispatchedUrl = null;
      const ac = new AbortController();
      const listener = () => {
        const url = getRoutePath();
        if (url !== lastDispatchedUrl) { lastDispatchedUrl = url; dispatchNormal(handler(url)); }
      };
      window.addEventListener('popstate', listener, { signal: ac.signal });
      window.addEventListener('hashchange', listener, { signal: ac.signal });
      listener();
      return { unsubscribe: () => ac.abort() };
    },
    worker: (scriptUrl, input, onResult, onError) => {
      let w;
      try { w = new Worker(scriptUrl, { type: 'module' }); }
      catch (e) { dispatchBackground(onError(e.message || 'Failed to create worker')); return { unsubscribe: () => {} }; }
      let terminated = false;
      w.onmessage = (e) => { if (!terminated) dispatchBackground(onResult(ensureString(e.data))); };
      w.onerror = (e) => { if (!terminated) dispatchBackground(onError(formatWorkerError(e))); };
      w.postMessage(input);
      return { unsubscribe: () => { terminated = true; w.terminate(); } };
    },
    workerWithProgress: (scriptUrl, input, onProgress, onResult, onError) => {
      let w;
      try { w = new Worker(scriptUrl, { type: 'module' }); }
      catch (e) { dispatchBackground(onError(e.message || 'Failed to create worker')); return { unsubscribe: () => {} }; }
      let terminated = false;
      w.onmessage = (e) => { if (!terminated) dispatchWorkerProgress(e.data, dispatchBackground, onProgress, onResult, onError); };
      w.onerror = (e) => { if (!terminated) dispatchBackground(onError(formatWorkerError(e))); };
      w.postMessage(input);
      return { unsubscribe: () => { terminated = true; w.terminate(); } };
    },
    poolWorker: (poolSize, scriptUrl, input, onResult, onError) => {
      const pool = getPool(poolSize, scriptUrl);
      const handle = pool.submit(input, (e) => dispatchBackground(onResult(ensureString(e.data))), (errMsg) => dispatchBackground(onError(errMsg)));
      return { unsubscribe: () => handle.cancel() };
    },
    poolWorkerWithProgress: (poolSize, scriptUrl, input, onProgress, onResult, onError) => {
      const pool = getPool(poolSize, scriptUrl);
      const handle = pool.submit(input, (e) => dispatchWorkerProgress(e.data, dispatchBackground, onProgress, onResult, onError), (errMsg) => dispatchBackground(onError(errMsg)));
      return { unsubscribe: () => handle.cancel() };
    },
    workerChannel: (scriptUrl, onMessage, onError) => {
      let w;
      try { w = new Worker(scriptUrl, { type: 'module' }); }
      catch (e) { dispatchBackground(onError(e.message || 'Failed to create worker')); return { unsubscribe: () => {} }; }
      let terminated = false;
      w.onmessage = (e) => { if (!terminated) dispatchBackground(onMessage(ensureString(e.data))); };
      w.onerror = (e) => { if (!terminated) dispatchBackground(onError(formatWorkerError(e))); };
      const prev = channelConnections.get(scriptUrl);
      if (prev) prev.terminate();
      channelConnections.set(scriptUrl, w);
      return { unsubscribe: () => { terminated = true; channelConnections.delete(scriptUrl); w.terminate(); } };
    },
    allocShared: (numBytes, handler) => {
      const n = ensureNumber(numBytes);
      try { dispatchNormal(handler(new SharedArrayBuffer(n))); }
      catch (e) { console.error('allocShared failed (COOP/COEP headers required):', e.message); }
      return { unsubscribe: () => {} };
    },
    workerShared: (buffer, scriptUrl, input, onResult, onError) => {
      let w;
      try { w = new Worker(scriptUrl, { type: 'module' }); }
      catch (e) { dispatchBackground(onError(e.message || 'Failed to create worker')); return { unsubscribe: () => {} }; }
      let terminated = false;
      w.onmessage = (e) => { if (!terminated) dispatchBackground(onResult(ensureString(e.data))); };
      w.onerror = (e) => { if (!terminated) dispatchBackground(onError(formatWorkerError(e))); };
      w.postMessage({ input, buffer }, []);
      return { unsubscribe: () => { terminated = true; w.terminate(); } };
    },
    allocImage: (width, height, handler) => {
      const w = ensureNumber(width); const h = ensureNumber(height);
      const id = bufferRegistry.allocateImage(w, h);
      if (id !== -1) { dispatchNormal(handler(mkBufferHandle(id, bufferRegistry.version(id), w, h))); }
      else { console.error('allocImage failed (COOP/COEP headers required)'); }
      return { unsubscribe: () => {} };
    },
    allocBuffer: (size, handler) => {
      const n = ensureNumber(size);
      const id = bufferRegistry.allocate(n);
      if (id !== -1) { dispatchNormal(handler(mkBufferHandle(id, bufferRegistry.version(id), n, 1))); }
      else { console.error('allocBuffer failed (COOP/COEP headers required)'); }
      return { unsubscribe: () => {} };
    },
    allocImageE: (width, height, handler, onError) => {
      const w = ensureNumber(width); const h = ensureNumber(height);
      const id = bufferRegistry.allocateImage(w, h);
      if (id !== -1) { dispatchNormal(handler(mkBufferHandle(id, bufferRegistry.version(id), w, h))); }
      else { dispatchNormal(onError('allocImage failed: COOP/COEP headers required')); }
      return { unsubscribe: () => {} };
    },
    allocBufferE: (size, handler, onError) => {
      const n = ensureNumber(size);
      const id = bufferRegistry.allocate(n);
      if (id !== -1) { dispatchNormal(handler(mkBufferHandle(id, bufferRegistry.version(id), n, 1))); }
      else { dispatchNormal(onError('allocBuffer failed: COOP/COEP headers required')); }
      return { unsubscribe: () => {} };
    }
  };
}

/**
 * Interprets Sub AST (leaf event sources) and creates subscriptions.
 * Sub contains all event sources that don't recursively contain Event.
 * Adding a new event source only requires adding a handler in makeLeafHandlers.
 */
function interpretSub(subEvent, dispatch, dispatchers = null) {
  const dispatchImmediate = dispatchers?.immediate || dispatch;
  const dispatchNormal = dispatchers?.normal || dispatch;
  const dispatchBackground = dispatchers?.background || dispatch;

  return subEvent(makeLeafHandlers(dispatchImmediate, dispatchNormal, dispatchBackground));
}

/**
 * Dispatch a worker message using the progress protocol.
 * Protocol: {type: 'progress', value} | {type: 'done', result} | {type: 'error', message} | raw data
 */
function dispatchWorkerProgress(data, dispatch, onProgress, onResult, onError) {
  if (data && typeof data === 'object') {
    if (data.type === 'progress') {
      dispatch(onProgress(String(data.value)));
    } else if (data.type === 'done') {
      dispatch(onResult(ensureString(data.result)));
    } else if (data.type === 'error') {
      dispatch(onError(data.message || 'Worker error'));
    } else {
      dispatch(onResult(ensureString(data)));
    }
  } else {
    dispatch(onResult(ensureString(data)));
  }
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
    toBool(e.ctrlKey),
    toBool(e.altKey),
    toBool(e.shiftKey),
    toBool(e.metaKey),
    toBool(e.repeat),
    BigInt(e.location ?? 0)
  )};
}

/**
 * Creates MouseEvent record for Agda (Scott-encoded, object format)
 */
function mkMouseEvent(e) {
  return {"mkMouseEvent": (cb) => cb["mkMouseEvent"](
    e.clientX,            // Float (mouseX)
    e.clientY,            // Float (mouseY)
    e.pageX,              // Float (pageX)
    e.pageY,              // Float (pageY)
    BigInt(e.button ?? 0),     // ℕ (button)
    BigInt(e.buttons ?? 0)     // ℕ (buttons)
  )};
}

/**
 * Unsubscribe
 */
export function unsubscribe(subscription) {
  if (subscription && typeof subscription.unsubscribe === 'function') {
    subscription.unsubscribe();
  }
}

