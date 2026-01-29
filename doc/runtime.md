# Agdelte Runtime

JavaScript runtime implementation for Agdelte applications.

## Overview

The runtime interprets Scott-encoded Agda data structures and executes them in the browser. **Key feature: No Virtual DOM** — uses reactive bindings like Svelte.

```
┌─────────────────────────────────────────────────────────────┐
│  Agda                                                        │
│  ReactiveApp { init, update, template }                      │
│  ↓ Compiled to JS (Scott encoding)                           │
├─────────────────────────────────────────────────────────────┤
│  Runtime                                                     │
│  runReactiveApp(app, container)                              │
│  ├─ renderNode(template) — create DOM, track bindings        │
│  ├─ dispatch(msg) — event loop                               │
│  └─ updateBindings(oldModel, newModel) — direct DOM updates  │
├─────────────────────────────────────────────────────────────┤
│  Binding Scopes (Phase 3)                                    │
│  Tree of scopes, each with own bindings                      │
│  On model change: check binding.extract(old) vs extract(new) │
│  If changed → update domNode directly (NO diffing!)          │
│  Destroyed scope → all child bindings cleaned up             │
└─────────────────────────────────────────────────────────────┘
```

## Main Loop (Reactive — No VDOM!)

```javascript
function runReactiveApp(app, container) {
  let model = app.init;
  const rootScope = createScope();  // Binding scopes (Phase 3)

  // 1. Initial render: create DOM, collect bindings in scopes
  const dom = renderNode(app.template, rootScope);
  container.appendChild(dom);

  function dispatch(msg) {
    const oldModel = model;

    // 2. Update model
    model = app.update(msg)(oldModel);

    // 3. Update only changed bindings (NO VDOM DIFF!)
    updateBindings(rootScope, oldModel, model);
    // Each scope updates its own bindings
    // Destroyed scopes (when condition false) clean up all child bindings
  }
}
```

**Key difference from Virtual DOM**: No tree reconstruction, no diffing. O(bindings) instead of O(tree).

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

**Note:** Agda `Bool` compiles to native JS `true`/`false`, not Scott-encoded.

## Reactive Rendering (No VDOM!)

### renderNode — Initial Render

Walk the template tree, create real DOM, collect bindings:

```javascript
function renderNode(node) {
  return node({
    text: (str) => document.createTextNode(str),

    bind: (binding) => {
      const value = binding.extract(model);
      const textNode = document.createTextNode(value);
      bindings.push({ node: textNode, binding });
      return textNode;
    },

    elem: (tag, attrs, children) => {
      const el = document.createElement(tag);
      // attrs and children are Agda lists — convert via listToArray()
      for (const attr of listToArray(attrs)) applyAttr(el, attr);
      for (const child of listToArray(children)) el.appendChild(renderNode(child));
      return el;
    },

    empty: () => null,

    when: (cond, innerNode) => {
      if (cond(model)) {               // Bool is native JS boolean
        return renderNode(innerNode);
      } else {
        return document.createComment('when');
      }
    },

    foreach: (_typeA, getList, render) => {
      // Note: first arg is implicit Agda type parameter
      const items = listToArray(getList(model));
      items.forEach((item, idx) => {
        container.appendChild(renderNode(render(item)(BigInt(idx))));
      });
    },

    // Phase 3: keyed list reconciliation
    foreachKeyed: (_typeA, getList, keyFn, render) => {
      // Same key → reuse DOM node; new key → create; removed → destroy
      // Uses data-key attribute for O(n) reconciliation
    },

    // Phase 3: conditional with CSS transitions
    whenT: (cond, transition, innerNode) => {
      // On enter: add enterClass, render node
      // On leave: add leaveClass, remove after duration ms
    }
  });
}
```

### updateBindings — On Model Change

No diffing — just check each binding with simple JS `!==`:

```javascript
function updateBindings(oldModel, newModel) {
  // Text bindings
  for (const { node, binding } of textBindings) {
    const oldVal = binding.extract(oldModel);
    const newVal = binding.extract(newModel);
    if (oldVal !== newVal) node.textContent = newVal;
  }

  // Attribute bindings
  for (const { node, binding, attrName } of attrBindings) {
    const oldVal = binding.extract(oldModel);
    const newVal = binding.extract(newModel);
    if (oldVal !== newVal) node.setAttribute(attrName, newVal);
  }

  // Style bindings
  for (const { node, binding, styleName } of styleBindings) {
    const oldVal = binding.extract(oldModel);
    const newVal = binding.extract(newModel);
    if (oldVal !== newVal) node.style.setProperty(styleName, newVal);
  }

  // Conditionals (when) — toggle visibility
  // Lists (foreach) — re-render on length change
}
```

**Performance**: O(bindings), not O(tree). Same approach as Svelte's compiled output.

**Note**: We use JS `!==` instead of Agda's `Binding.equals` because Agda stdlib's string equality (`_≈?_` from Data.String.Properties) causes stack overflow in JS due to deep proof term evaluation.

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
        .then(text => executeTask(onOk(text), onSuccess, onError))
        .catch(err => executeTask(onErr(err.message), onSuccess, onError));
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
  const eventSpec = subs(model);
  const newFingerprint = serializeEvent(eventSpec);

  // Only resubscribe if structure changed
  if (newFingerprint === currentEventFingerprint) return;

  unsubscribe(currentSubscription);
  currentSubscription = interpretEvent(eventSpec, dispatch);
  currentEventFingerprint = newFingerprint;
}
```

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
| `foldE` | Maintain internal state; on inner event: `state = step(val, state)`, dispatch state |
| `mapFilterE` | On inner event: apply `f`, dispatch if `just`, skip if `nothing` |
| `switchE` | Subscribe to initial; on meta-event: unsubscribe old, subscribe new |

## Files

| File | Purpose |
|------|---------|
| `runtime/reactive.js` | Main: `runReactiveApp`, `mountReactive`, renderNode, updateBindings |
| `runtime/reactive-auto.js` | Auto-loader: mounts based on `data-agdelte` attribute |
| `runtime/events.js` | interpretEvent, subscribe/unsubscribe |

## Usage

### Auto-loader (recommended)

```html
<div id="app" data-agdelte="Counter"></div>
<script type="module" src="../runtime/reactive-auto.js"></script>
```

### Programmatic

```javascript
import { mountReactive } from './runtime/reactive.js';

await mountReactive('Counter', document.getElementById('app'));

// Custom build directory
await mountReactive('MyApp', '#app', { buildDir: './dist' });
```

### Direct import

```javascript
import { runReactiveApp } from './runtime/reactive.js';
import Counter from './_build/jAgda.Counter.mjs';

await runReactiveApp(Counter, document.getElementById('app'));
```
