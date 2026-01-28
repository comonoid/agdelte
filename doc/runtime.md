# Agdelte Runtime

JavaScript runtime implementation for Agdelte applications.

## Overview

The runtime interprets Scott-encoded Agda data structures and executes them in the browser:

```
┌─────────────────────────────────────────────────────────────┐
│  Agda                                                        │
│  App { init, update, view, subs, command }                   │
│  ↓ Compiled to JS (Scott encoding)                           │
├─────────────────────────────────────────────────────────────┤
│  Runtime (index.js)                                          │
│  runApp(app, container)                                      │
│  ├─ dispatch(msg) — event loop                               │
│  ├─ executeCmd(cmd) — interpret commands                     │
│  ├─ executeTask(task) — interpret monadic chains             │
│  └─ updateSubscriptions() — manage event listeners           │
├─────────────────────────────────────────────────────────────┤
│  DOM (dom.js)                                                │
│  createElement, patch — VDOM diffing                         │
├─────────────────────────────────────────────────────────────┤
│  Events (events.js)                                          │
│  interpretEvent — subscription management                    │
│  Timers, Keyboard, WebSocket, Routing                        │
└─────────────────────────────────────────────────────────────┘
```

## Main Loop

```javascript
function runApp(app, container) {
  let model = app.init;

  function dispatch(msg) {
    // 1. Get command BEFORE updating model
    const cmd = app.command(msg)(model);

    // 2. Update model
    model = app.update(msg)(model);

    // 3. Execute command
    executeCmd(cmd, dispatch);

    // 4. Re-render
    render();

    // 5. Update subscriptions (with fingerprint comparison)
    updateSubscriptions();
  }

  render();
  updateSubscriptions();
}
```

## Scott Encoding

Agda data types compile to functions that pattern match:

```agda
data Cmd A where
  ε : Cmd A
  httpGet : String → (String → A) → (String → A) → Cmd A
```

Compiles to:

```javascript
cmd({
  'ε': () => { /* empty command */ },
  'httpGet': (url, onSuccess, onError) => {
    fetch(url)
      .then(r => r.text())
      .then(text => dispatch(onSuccess(text)))
      .catch(err => dispatch(onError(err.message)));
  }
});
```

## Command Execution

Commands are interpreted and executed once:

| Command | Implementation |
|---------|---------------|
| `ε` | No-op |
| `_<>_` | Execute both in parallel |
| `httpGet` | `fetch()` → dispatch result |
| `httpPost` | `fetch()` with POST → dispatch result |
| `attempt` | Execute Task chain → dispatch Result |
| `focus` | `querySelector().focus()` |
| `blur` | `querySelector().blur()` |
| `scrollTo` | `window.scrollTo()` |
| `scrollIntoView` | `querySelector().scrollIntoView()` |
| `writeClipboard` | `navigator.clipboard.writeText()` |
| `readClipboard` | `navigator.clipboard.readText()` → dispatch |
| `getItem` | `localStorage.getItem()` → dispatch Maybe |
| `setItem` | `localStorage.setItem()` |
| `removeItem` | `localStorage.removeItem()` |
| `wsSend` | `ws.send()` (to existing connection) |
| `pushUrl` | `history.pushState()` |
| `replaceUrl` | `history.replaceState()` |
| `back` | `history.back()` |
| `forward` | `history.forward()` |

## Task Execution

Tasks are monadic chains interpreted recursively:

```javascript
function executeTask(task, onSuccess, onError) {
  task({
    'pure': (value) => onSuccess(value),
    'fail': (error) => onError(error),
    'httpGet': (url, onOk, onErr) => {
      fetch(url)
        .then(r => r.text())
        .then(text => {
          // Continue with next task in chain
          const nextTask = onOk(text);
          executeTask(nextTask, onSuccess, onError);
        })
        .catch(err => {
          const nextTask = onErr(err.message);
          executeTask(nextTask, onSuccess, onError);
        });
    }
  });
}
```

## Subscription Management

### Fingerprint Comparison

Critical optimization for WebSocket and other stateful subscriptions:

```javascript
function serializeEvent(event) {
  return event({
    never: () => 'never',
    interval: (ms, msg) => `interval(${ms})`,
    wsConnect: (url, handler) => `wsConnect(${url})`,
    merge: (e1, e2) => `merge(${serializeEvent(e1)},${serializeEvent(e2)})`,
    // ...
  });
}

function updateSubscriptions() {
  const eventSpec = app.subs(model);
  const newFingerprint = serializeEvent(eventSpec);

  // Only resubscribe if structure changed
  if (newFingerprint === currentEventFingerprint) {
    return;
  }

  unsubscribe(currentSubscription);
  currentSubscription = interpretEvent(eventSpec, dispatch);
  currentEventFingerprint = newFingerprint;
}
```

This prevents WebSocket reconnection when only message handler changes.

### Event Interpretation

Events are AST nodes interpreted by runtime:

| Event | Interpretation |
|-------|---------------|
| `never` | No-op |
| `interval` | `setInterval()` |
| `timeout` | `setTimeout()` |
| `onKeyDown` | `document.addEventListener('keydown')` |
| `onKeyUp` | `document.addEventListener('keyup')` |
| `wsConnect` | `new WebSocket()` with handlers |
| `onUrlChange` | `window.addEventListener('popstate')` |
| `merge` | Interpret both children |
| `debounce` | Wrap inner with debounce logic |
| `throttle` | Wrap inner with throttle logic |

## DOM Patching

Virtual DOM diffing with handler preservation:

```javascript
function patch(dom, oldVdom, newVdom, dispatch) {
  // Text nodes
  if (newVdom.tag === 'TEXT') {
    if (oldVdom.tag === 'TEXT' && oldVdom.text === newVdom.text) {
      return dom; // unchanged
    }
    return document.createTextNode(newVdom.text);
  }

  // Different tags → replace
  if (oldVdom.tag !== newVdom.tag) {
    const newDom = createElement(newVdom, dispatch);
    dom.parentNode.replaceChild(newDom, dom);
    return newDom;
  }

  // Same tag → update attrs and children
  patchAttrs(dom, oldVdom.attrs, newVdom.attrs, dispatch);
  patchChildren(dom, oldVdom.children, newVdom.children, dispatch);
  return dom;
}
```

### Handler Updates

Handlers are stored on DOM elements and updated in place:

```javascript
// Store handler reference
el._handlers = el._handlers || {};
el._handlers['click'] = msg;

// Event listener uses stored reference
el.addEventListener('click', () => {
  const handler = el._handlers['click'];
  if (handler) dispatch(handler);
});
```

This allows updating handlers without removing/re-adding event listeners.

## Files

| File | Purpose |
|------|---------|
| `runtime/index.js` | Main entry: `mount`, `mountModule`, `runApp` |
| `runtime/dom.js` | createElement, patch, VDOM diffing |
| `runtime/events.js` | interpretEvent, subscribe/unsubscribe |

## Exports

| Export | Description |
|--------|-------------|
| `mount(app, container)` | Mount compiled App (high-level) |
| `mountModule(name, container, opts)` | Dynamic import + mount |
| `runApp(config, container)` | Low-level mount with manual config |
| `createElement(vdom, dispatch)` | Create DOM from VDOM |
| `patch(dom, oldVdom, newVdom, dispatch)` | Diff and patch DOM |
| `interpretEvent(event, dispatch)` | Set up event subscriptions |
| `debounce(fn, ms)` | Debounce helper |
| `throttle(fn, ms)` | Throttle helper |

## Usage

### High-level API (recommended)

```javascript
import { mount } from 'agdelte/runtime';
import Counter from './_build/jAgda.Counter.mjs';

// Mount with imported module
mount(Counter.app, '#app');

// Or pass module directly (auto-extracts .app)
mount(Counter, '#app');
```

### Dynamic import

```javascript
import { mountModule } from 'agdelte/runtime';

// Loads module dynamically
await mountModule('Counter', '#app');

// Custom build directory
await mountModule('MyApp', '#app', { buildDir: './dist' });
```

### Low-level API

```javascript
import { runApp } from 'agdelte/runtime';

// Manual extraction (rarely needed)
// Agda records compile to: { "record": f => f["record"](fields...) }
const app = {
  init:    compiledApp["record"]({"record": (i,u,v,s,c) => i}),
  update:  compiledApp["record"]({"record": (i,u,v,s,c) => u}),
  view:    compiledApp["record"]({"record": (i,u,v,s,c) => v}),
  subs:    compiledApp["record"]({"record": (i,u,v,s,c) => s}),
  command: compiledApp["record"]({"record": (i,u,v,s,c) => c})
};

runApp(app, document.getElementById('app'));
```

### Minimal HTML

```html
<!DOCTYPE html>
<html>
<body>
  <div id="app"></div>
  <script type="module">
    import { mount } from './runtime/index.js';
    import App from './_build/jAgda.MyApp.mjs';
    mount(App, '#app');
  </script>
</body>
</html>
```
