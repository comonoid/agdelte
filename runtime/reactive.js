/**
 * Agdelte Reactive Runtime
 * Renders ReactiveApp with direct DOM updates (no Virtual DOM)
 * Like Svelte - bindings track which DOM nodes need updating
 */

import { interpretEvent, unsubscribe, wsConnections } from './events.js';

/**
 * Execute Task (monadic chain)
 */
function executeTask(task, onSuccess, onError) {
  task({
    'pure': (value) => onSuccess(value),
    'fail': (error) => onError(error),
    'httpGet': (url, onOk, onErr) => {
      fetch(url)
        .then(async (response) => {
          if (!response.ok) throw new Error(`HTTP ${response.status}`);
          return response.text();
        })
        .then((text) => executeTask(onOk(text), onSuccess, onError))
        .catch((error) => executeTask(onErr(error.message), onSuccess, onError));
    },
    'httpPost': (url, body, onOk, onErr) => {
      fetch(url, { method: 'POST', headers: { 'Content-Type': 'application/json' }, body })
        .then(async (response) => {
          if (!response.ok) throw new Error(`HTTP ${response.status}`);
          return response.text();
        })
        .then((text) => executeTask(onOk(text), onSuccess, onError))
        .catch((error) => executeTask(onErr(error.message), onSuccess, onError));
    }
  });
}

/**
 * Execute Cmd
 */
function executeCmd(cmd, dispatch) {
  if (!cmd) return;

  cmd({
    'ε': () => {},
    '_<>_': (cmd1, cmd2) => {
      executeCmd(cmd1, dispatch);
      executeCmd(cmd2, dispatch);
    },
    'httpGet': (url, onSuccess, onError) => {
      fetch(url)
        .then(async (r) => r.ok ? r.text() : Promise.reject(new Error(`HTTP ${r.status}`)))
        .then((text) => dispatch(onSuccess(text)))
        .catch((error) => dispatch(onError(error.message)));
    },
    'httpPost': (url, body, onSuccess, onError) => {
      fetch(url, { method: 'POST', headers: { 'Content-Type': 'application/json' }, body })
        .then(async (r) => r.ok ? r.text() : Promise.reject(new Error(`HTTP ${r.status}`)))
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
    'focus': (sel) => document.querySelector(sel)?.focus(),
    'blur': (sel) => document.querySelector(sel)?.blur(),
    'scrollTo': (x, y) => window.scrollTo(Number(x), Number(y)),
    'scrollIntoView': (sel) => document.querySelector(sel)?.scrollIntoView({ behavior: 'smooth' }),
    'writeClipboard': (text) => navigator.clipboard.writeText(text).catch(() => {}),
    'readClipboard': (handler) => navigator.clipboard.readText().then((t) => dispatch(handler(t))).catch(() => dispatch(handler(''))),
    'getItem': (key, handler) => {
      const value = localStorage.getItem(key);
      dispatch(handler(value !== null ? (cb) => cb['just'](value) : (cb) => cb['nothing']()));
    },
    'setItem': (key, value) => localStorage.setItem(key, value),
    'removeItem': (key) => localStorage.removeItem(key),
    'wsSend': (url, message) => {
      const ws = wsConnections.get(url);
      if (ws?.readyState === WebSocket.OPEN) ws.send(message);
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

/**
 * Create reactive app runner
 */
export async function runReactiveApp(moduleExports, container, options = {}) {
  await loadNodeModule();

  // Extract app, subs, cmd from module
  const appRecord = moduleExports.app;
  const subsFunc = moduleExports.subs || null;
  const cmdFunc = moduleExports.cmd || null;

  // Extract ReactiveApp fields
  const init = NodeModule.ReactiveApp.init(appRecord);
  const update = NodeModule.ReactiveApp.update(appRecord);
  const template = NodeModule.ReactiveApp.template(appRecord);

  // State
  let model = init;
  const bindings = [];       // text bindings: { node, binding }
  const attrBindings = [];   // attr bindings: { node, binding, attrName }
  const styleBindings = [];  // style bindings: { node, binding, styleName }
  const conditionals = [];   // when: { node, parent, placeholder, cond, rendered }
  const lists = [];          // foreach: { node, parent, getList, render, items }

  let currentSubscription = null;
  let currentEventFingerprint = null;
  let isUpdating = false;
  let pendingMessages = [];

  /**
   * Dispatch message
   */
  function dispatch(msg) {
    if (isUpdating) {
      pendingMessages.push(msg);
      return;
    }

    isUpdating = true;
    try {
      const oldModel = model;

      // Execute command before updating
      if (cmdFunc) {
        const cmd = cmdFunc(msg)(model);
        executeCmd(cmd, dispatch);
      }

      // Update model
      model = update(msg)(oldModel);

      // Update bindings
      updateBindings(oldModel, model);

      // Update subscriptions
      updateSubscriptions();

      // Process pending
      while (pendingMessages.length > 0) {
        const nextMsg = pendingMessages.shift();
        const nextOld = model;
        if (cmdFunc) {
          const nextCmd = cmdFunc(nextMsg)(model);
          executeCmd(nextCmd, dispatch);
        }
        model = update(nextMsg)(nextOld);
        updateBindings(nextOld, model);
        updateSubscriptions();
      }
    } finally {
      isUpdating = false;
    }
  }

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
        bindings.push({ node: textNode, binding });
        return textNode;
      },

      elem: (tag, attrs, children) => {
        const el = document.createElement(tag);

        // Apply attributes (convert Agda list to JS array)
        const attrArray = listToArray(attrs);
        for (const attr of attrArray) {
          applyAttr(el, attr);
        }

        // Render children (convert Agda list to JS array)
        const childArray = listToArray(children);
        for (const child of childArray) {
          const childNode = renderNode(child);
          if (childNode) el.appendChild(childNode);
        }

        return el;
      },

      empty: () => null,

      when: (cond, innerNode) => {
        const shouldShow = !!cond(model);  // Bool is native JS boolean

        if (shouldShow) {
          const rendered = renderNode(innerNode);
          conditionals.push({ cond, innerNode, node: rendered, rendered: true });
          return rendered;
        } else {
          const placeholder = document.createComment('when');
          conditionals.push({ cond, innerNode, node: placeholder, rendered: false, placeholder });
          return placeholder;
        }
      },

      foreach: (_typeA, getList, render) => {
        const container = document.createDocumentFragment();
        const marker = document.createComment('foreach');
        container.appendChild(marker);

        const items = getList(model);
        const renderedItems = [];

        // Convert list
        const itemArray = listToArray(items);

        itemArray.forEach((item, idx) => {
          const itemNode = renderNode(render(item)(BigInt(idx)));
          if (itemNode) {
            renderedItems.push({ item, node: itemNode });
            container.appendChild(itemNode);
          }
        });

        lists.push({ marker, getList, render, renderedItems });

        return container;
      }
    });
  }

  /**
   * Apply attribute to element
   */
  function applyAttr(el, attr) {
    attr({
      attr: (name, value) => {
        if (name === 'disabled' || name === 'checked') {
          if (value === 'true') el.setAttribute(name, '');
          // if empty, don't set
        } else {
          el.setAttribute(name, value);
        }
      },
      attrBind: (name, binding) => {
        const extract = NodeModule.Binding.extract(binding);
        const value = extract(model);
        if (name === 'disabled' || name === 'checked') {
          if (value === 'true') el.setAttribute(name, '');
          else el.removeAttribute(name);
        } else {
          el.setAttribute(name, value);
        }
        attrBindings.push({ node: el, binding, attrName: name });
      },
      on: (event, msg) => {
        el.addEventListener(event, (e) => {
          // Prevent default for links with onClick
          if (el.tagName === 'A' && event === 'click') {
            e.preventDefault();
          }
          dispatch(msg);
        });
      },
      onValue: (event, handler) => {
        el.addEventListener(event, (e) => {
          const value = event === 'keydown' || event === 'keyup'
            ? e.key
            : e.target.value || '';
          dispatch(handler(value));
        });
      },
      style: (name, value) => {
        el.style.setProperty(name, value);
      },
      styleBind: (name, binding) => {
        const extract = NodeModule.Binding.extract(binding);
        el.style.setProperty(name, extract(model));
        styleBindings.push({ node: el, binding, styleName: name });
      }
    });
  }

  /**
   * Convert Agda list to JS array
   */
  function listToArray(list) {
    // Handle edge cases
    if (!list) return [];
    if (Array.isArray(list)) return list;
    if (typeof list !== 'function') {
      console.warn('listToArray: expected function, got', typeof list, list);
      return [];
    }

    const result = [];
    let current = list;
    while (true) {
      if (typeof current !== 'function') {
        console.warn('listToArray: tail is not a function', current);
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
    return result;
  }

  /**
   * Update all bindings
   */
  function updateBindings(oldModel, newModel) {
    // Text bindings - use simple JS equality (Agda's equals causes stack overflow)
    for (const { node, binding } of bindings) {
      const extract = NodeModule.Binding.extract(binding);
      const oldVal = extract(oldModel);
      const newVal = extract(newModel);

      if (oldVal !== newVal) {
        node.textContent = newVal;
      }
    }

    // Attribute bindings
    for (const { node, binding, attrName } of attrBindings) {
      const extract = NodeModule.Binding.extract(binding);
      const oldVal = extract(oldModel);
      const newVal = extract(newModel);

      if (oldVal !== newVal) {
        if (attrName === 'disabled' || attrName === 'checked') {
          if (newVal === 'true') node.setAttribute(attrName, '');
          else node.removeAttribute(attrName);
        } else {
          node.setAttribute(attrName, newVal);
        }
      }
    }

    // Style bindings
    for (const { node, binding, styleName } of styleBindings) {
      const extract = NodeModule.Binding.extract(binding);
      const oldVal = extract(oldModel);
      const newVal = extract(newModel);

      if (oldVal !== newVal) {
        node.style.setProperty(styleName, newVal);
      }
    }

    // Conditional (when) - simple re-render when condition changes
    for (const cond of conditionals) {
      const showBool = !!cond.cond(newModel);  // Bool is native JS boolean

      if (showBool !== cond.rendered) {
        if (showBool) {
          // Render and insert
          const newNode = renderNode(cond.innerNode);
          cond.node.replaceWith(newNode);
          cond.node = newNode;
          cond.rendered = true;
        } else {
          // Remove and put placeholder
          const placeholder = document.createComment('when');
          cond.node.replaceWith(placeholder);
          cond.node = placeholder;
          cond.rendered = false;
        }
      }
    }

    // Lists (foreach) - simple re-render
    for (const list of lists) {
      const newItems = listToArray(list.getList(newModel));
      const oldItems = list.renderedItems;

      // Simple approach: if length changed, rebuild
      if (newItems.length !== oldItems.length) {
        // Remove old items
        for (const { node } of oldItems) {
          node.remove();
        }

        // Render new items
        list.renderedItems = [];
        const parent = list.marker.parentNode;
        let insertBefore = list.marker.nextSibling;

        newItems.forEach((item, idx) => {
          const itemNode = renderNode(list.render(item)(BigInt(idx)));
          if (itemNode) {
            list.renderedItems.push({ item, node: itemNode });
            parent.insertBefore(itemNode, insertBefore);
          }
        });
      }
      // TODO: more efficient diffing for lists
    }
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
      onKeyDown: (handler) => 'onKeyDown',
      onKeyUp: (handler) => 'onKeyUp',
      onKeys: (pairs) => 'onKeys',
      httpGet: (url, ok, err) => `httpGet(${url})`,
      httpPost: (url, body, ok, err) => `httpPost(${url})`,
      merge: (e1, e2) => `merge(${serializeEvent(e1)},${serializeEvent(e2)})`,
      debounce: (ms, inner) => `debounce(${ms})`,
      throttle: (ms, inner) => `throttle(${ms})`,
      wsConnect: (url, handler) => `wsConnect(${url})`,
      onUrlChange: (handler) => 'onUrlChange'
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

    currentSubscription = interpretEvent(eventSpec, dispatch);
    currentEventFingerprint = newFingerprint;
  }

  // Initial render
  container.innerHTML = '';
  const dom = renderNode(template);
  if (dom) {
    if (dom.nodeType === Node.DOCUMENT_FRAGMENT_NODE) {
      container.appendChild(dom);
    } else {
      container.appendChild(dom);
    }
  }

  // Initial subscriptions
  updateSubscriptions();

  console.log(`Reactive app mounted: ${bindings.length} text bindings, ${attrBindings.length} attr bindings, ${styleBindings.length} style bindings`);

  return {
    dispatch,
    getModel: () => model,
    getContainer: () => container,
    destroy: () => {
      if (currentSubscription) {
        unsubscribe(currentSubscription);
      }
      container.innerHTML = '';
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
    containerEl.innerHTML = `
      <div class="error">
        <strong>Failed to load ${moduleName}:</strong> ${e.message}
        <pre>${e.stack}</pre>
      </div>
    `;
    throw e;
  }
}

export { interpretEvent, unsubscribe } from './events.js';
