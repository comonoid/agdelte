/**
 * Agdelte Runtime - Main Entry Point
 * Runs an Elm-like application in the browser
 */

import { createElement, patch } from './dom.js';
import { interpretEvent, unsubscribe, wsConnections, channelConnections } from './events.js';

/**
 * Interprets and executes a Task (monadic chain)
 * @param {Object} task - Scott-encoded Task
 * @param {Function} onSuccess - callback on success (value)
 * @param {Function} onError - callback on error (string)
 */
function executeTask(task, onSuccess, onError) {
  task({
    // pure(a) - successful completion
    'pure': (value) => {
      onSuccess(value);
    },

    // fail(e) - error
    'fail': (error) => {
      onError(error);
    },

    // httpGet(url, onOk, onErr) - HTTP GET with continuation
    'httpGet': (url, onOk, onErr) => {
      fetch(url)
        .then(async (response) => {
          if (!response.ok) {
            throw new Error(`HTTP ${response.status}: ${response.statusText}`);
          }
          return response.text();
        })
        .then((text) => {
          // Continue with result
          const nextTask = onOk(text);
          executeTask(nextTask, onSuccess, onError);
        })
        .catch((error) => {
          // Continue with error (onErr continuation)
          const nextTask = onErr(error.message);
          executeTask(nextTask, onSuccess, onError);
        });
    },

    // httpPost(url, body, onOk, onErr) - HTTP POST with continuation
    'httpPost': (url, body, onOk, onErr) => {
      fetch(url, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body
      })
        .then(async (response) => {
          if (!response.ok) {
            throw new Error(`HTTP ${response.status}: ${response.statusText}`);
          }
          return response.text();
        })
        .then((text) => {
          const nextTask = onOk(text);
          executeTask(nextTask, onSuccess, onError);
        })
        .catch((error) => {
          const nextTask = onErr(error.message);
          executeTask(nextTask, onSuccess, onError);
        });
    }
  });
}

/**
 * Interprets and executes a command (Cmd)
 * @param {Object} cmd - Scott-encoded Cmd
 * @param {Function} dispatch - message dispatch function
 */
function executeCmd(cmd, dispatch) {
  cmd({
    // ε - empty command
    'ε': () => {},

    // _<>_ - command composition (parallel execution)
    '_<>_': (cmd1, cmd2) => {
      executeCmd(cmd1, dispatch);
      executeCmd(cmd2, dispatch);
    },

    // httpGet - HTTP GET request (simple API)
    'httpGet': (url, onSuccess, onError) => {
      fetch(url)
        .then(async (response) => {
          if (!response.ok) {
            throw new Error(`HTTP ${response.status}: ${response.statusText}`);
          }
          return response.text();
        })
        .then((text) => dispatch(onSuccess(text)))
        .catch((error) => dispatch(onError(error.message)));
    },

    // httpPost - HTTP POST request (simple API)
    'httpPost': (url, body, onSuccess, onError) => {
      fetch(url, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body
      })
        .then(async (response) => {
          if (!response.ok) {
            throw new Error(`HTTP ${response.status}: ${response.statusText}`);
          }
          return response.text();
        })
        .then((text) => dispatch(onSuccess(text)))
        .catch((error) => dispatch(onError(error.message)));
    },

    // attempt - run Task (monadic API)
    // Result: ok(value) or err(error)
    'attempt': (task, handler) => {
      executeTask(
        task,
        // onSuccess: Result.ok
        (value) => {
          const result = (cb) => cb['ok'](value);
          dispatch(handler(result));
        },
        // onError: Result.err
        (error) => {
          const result = (cb) => cb['err'](error);
          dispatch(handler(result));
        }
      );
    },

    // === DOM effects ===
    'focus': (selector) => {
      const el = document.querySelector(selector);
      if (el) el.focus();
    },

    'blur': (selector) => {
      const el = document.querySelector(selector);
      if (el) el.blur();
    },

    'scrollTo': (x, y) => {
      const xNum = typeof x === 'bigint' ? Number(x) : x;
      const yNum = typeof y === 'bigint' ? Number(y) : y;
      window.scrollTo(xNum, yNum);
    },

    'scrollIntoView': (selector) => {
      const el = document.querySelector(selector);
      if (el) el.scrollIntoView({ behavior: 'smooth' });
    },

    // === Clipboard ===
    'writeClipboard': (text) => {
      navigator.clipboard.writeText(text).catch(console.error);
    },

    'readClipboard': (handler) => {
      navigator.clipboard.readText()
        .then((text) => dispatch(handler(text)))
        .catch(() => dispatch(handler('')));
    },

    // === LocalStorage ===
    'getItem': (key, handler) => {
      const value = localStorage.getItem(key);
      // Maybe: just(x) or nothing
      const maybe = value !== null
        ? (cb) => cb['just'](value)
        : (cb) => cb['nothing']();
      dispatch(handler(maybe));
    },

    'setItem': (key, value) => {
      localStorage.setItem(key, value);
    },

    'removeItem': (key) => {
      localStorage.removeItem(key);
    },

    // === WebSocket ===
    'wsSend': (url, message) => {
      const ws = wsConnections.get(url);
      if (ws && ws.readyState === WebSocket.OPEN) {
        ws.send(message);
      }
    },

    // === Worker channel ===
    'channelSend': (scriptUrl, message) => {
      const w = channelConnections.get(scriptUrl);
      if (w) {
        w.postMessage(message);
      }
    },

    // === Routing ===
    'pushUrl': (url) => {
      history.pushState(null, '', url);
    },

    'replaceUrl': (url) => {
      history.replaceState(null, '', url);
    },

    'back': () => {
      history.back();
    },

    'forward': () => {
      history.forward();
    }
  });
}

/**
 * Run application
 * @param {Object} app - Compiled Agda application
 * @param {HTMLElement} container - DOM container
 * @returns {Object} - API for controlling the application
 */
export function runApp(app, container) {
  // Application state
  let model = app.init;
  let currentVdom = null;
  let currentDom = null;
  let currentSubscription = null;
  let isUpdating = false;
  let pendingMessages = [];

  // Message dispatcher
  function dispatch(msg) {
    if (isUpdating) {
      // Accumulate messages during update
      pendingMessages.push(msg);
      return;
    }

    isUpdating = true;

    try {
      // Get command BEFORE updating model (so command has access to old model)
      const cmd = app.command(msg)(model);

      // Update model
      model = app.update(msg)(model);

      // Execute command
      executeCmd(cmd, dispatch);

      // Re-render
      render();

      // Update subscriptions
      updateSubscriptions();

      // Process accumulated messages
      while (pendingMessages.length > 0) {
        const nextMsg = pendingMessages.shift();
        const nextCmd = app.command(nextMsg)(model);
        model = app.update(nextMsg)(model);
        executeCmd(nextCmd, dispatch);
        render();
        updateSubscriptions();
      }
    } finally {
      isUpdating = false;
    }
  }

  // Rendering
  function render() {
    const newVdom = app.view(model);

    if (currentDom === null) {
      // First render - clear container
      container.innerHTML = '';
      currentDom = createElement(newVdom, dispatch);
      container.appendChild(currentDom);
    } else {
      // Patching
      currentDom = patch(currentDom, currentVdom, newVdom, dispatch);
    }

    currentVdom = newVdom;
  }

  // Serialize Event AST for comparison
  function serializeEvent(event) {
    if (!event) return 'null';

    return event({
      never: () => 'never',
      interval: (ms, msg) => `interval(${ms})`,
      timeout: (ms, msg) => `timeout(${ms})`,
      onKeyDown: (handler) => 'onKeyDown',
      onKeyUp: (handler) => 'onKeyUp',
      httpGet: (url, onSuccess, onError) => `httpGet(${url})`,
      httpPost: (url, body, onSuccess, onError) => `httpPost(${url})`,
      merge: (e1, e2) => `merge(${serializeEvent(e1)},${serializeEvent(e2)})`,
      debounce: (ms, inner) => `debounce(${ms},${serializeEvent(inner)})`,
      throttle: (ms, inner) => `throttle(${ms},${serializeEvent(inner)})`,
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

  // Current subscription fingerprint
  let currentEventFingerprint = null;

  // Update event subscriptions
  // Strategy: compare fingerprints, resubscribe only on change
  function updateSubscriptions() {
    // Get new Event AST
    const eventSpec = app.subs(model);
    const newFingerprint = serializeEvent(eventSpec);

    // If subscription unchanged, do nothing
    if (newFingerprint === currentEventFingerprint) {
      return;
    }

    // Unsubscribe from old
    if (currentSubscription) {
      unsubscribe(currentSubscription);
    }

    // Interpret and subscribe
    currentSubscription = interpretEvent(eventSpec, dispatch);
    currentEventFingerprint = newFingerprint;
  }

  // Initialization
  render();
  updateSubscriptions();

  // Public API
  return {
    // Dispatch message
    dispatch,

    // Get current model
    getModel: () => model,

    // Get current DOM
    getContainer: () => container,

    // Force re-render
    forceRender: render,

    // Destroy application
    destroy: () => {
      if (currentSubscription) {
        unsubscribe(currentSubscription);
        currentSubscription = null;
      }
      container.innerHTML = '';
    }
  };
}

/**
 * Extract App fields from Scott-encoded record
 *
 * Agda records compile to: { "record": f => f["record"](field1, field2, ...) }
 * Access pattern: app["record"]({"record": (f1,f2,f3,f4,f5) => f1})
 */
function extractApp(compiledApp) {
  return {
    init:    compiledApp["record"]({"record": (i,u,v,s,c) => i}),
    update:  compiledApp["record"]({"record": (i,u,v,s,c) => u}),
    view:    compiledApp["record"]({"record": (i,u,v,s,c) => v}),
    subs:    compiledApp["record"]({"record": (i,u,v,s,c) => s}),
    command: compiledApp["record"]({"record": (i,u,v,s,c) => c})
  };
}

/**
 * Mount a compiled Agda App
 *
 * @param {Object|Function} appOrModule - Either a Scott-encoded App, or a module with .app
 * @param {HTMLElement|string} container - DOM element or selector
 * @returns {Object} App instance with dispatch, getModel, destroy, etc.
 *
 * @example
 * // With imported module
 * import Counter from './_build/jAgda.Counter.mjs';
 * mount(Counter.app, '#app');
 *
 * @example
 * // With module object
 * import Counter from './_build/jAgda.Counter.mjs';
 * mount(Counter, '#app');  // auto-extracts .app
 */
export function mount(appOrModule, container) {
  // Resolve container
  const containerEl = typeof container === 'string'
    ? document.querySelector(container)
    : container;

  if (!containerEl) {
    throw new Error(`Container not found: ${container}`);
  }

  // Extract app - handle both Module.app and raw App
  const compiledApp = typeof appOrModule === 'function'
    ? appOrModule  // Already a Scott-encoded App
    : appOrModule.app;  // Module with .app export

  if (!compiledApp) {
    throw new Error('No app found. Ensure module exports `app : App Model Msg`');
  }

  // Extract fields via Scott encoding
  const app = extractApp(compiledApp);

  // Run the app
  return runApp(app, containerEl);
}

/**
 * Mount with dynamic import (async)
 *
 * @param {string} moduleName - Module name (e.g., "Counter", "Keyboard")
 * @param {HTMLElement|string} container - DOM element or selector
 * @param {Object} [options] - Configuration
 * @param {string} [options.buildDir="../_build"] - Build directory path
 * @param {string} [options.prefix="jAgda."] - Module filename prefix
 * @returns {Promise<Object>} App instance
 *
 * @example
 * mountModule('Counter', '#app');
 * mountModule('Keyboard', '#app', { buildDir: './_build' });
 */
export async function mountModule(moduleName, container, options = {}) {
  const {
    buildDir = '../_build',
    prefix = 'jAgda.'
  } = options;

  const modulePath = `${buildDir}/${prefix}${moduleName}.mjs`;

  try {
    const module = await import(modulePath);
    return mount(module.default, container);
  } catch (e) {
    // Provide helpful error
    const containerEl = typeof container === 'string'
      ? document.querySelector(container)
      : container;

    if (containerEl) {
      containerEl.innerHTML = `
        <div style="background:rgba(233,69,96,0.2);border:1px solid #e94560;padding:1rem;border-radius:8px;">
          <strong>Failed to load ${moduleName}:</strong> ${e.message}
          <pre style="margin-top:0.5rem;font-size:0.85rem;overflow-x:auto;">${e.stack}</pre>
        </div>
      `;
    }
    throw e;
  }
}

// Re-export for convenience
export { createElement, patch } from './dom.js';
export { interpretEvent, subscribe, unsubscribe, debounce, throttle } from './events.js';
