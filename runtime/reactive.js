/**
 * Agdelte Reactive Runtime
 * Renders ReactiveApp with direct DOM updates (no Virtual DOM)
 * Like Svelte - bindings track which DOM nodes need updating
 *
 * Phase 3: Binding scopes, keyed foreach, when transitions
 */

import { interpretEvent, unsubscribe, wsConnections } from './events.js';

// ─────────────────────────────────────────────────────────────────────
// SVG/MathML namespace support
// ─────────────────────────────────────────────────────────────────────

const SVG_NS = 'http://www.w3.org/2000/svg';
const MATHML_NS = 'http://www.w3.org/1998/Math/MathML';

// Namespaced attributes (xlink:href, xml:lang, etc.)
const ATTR_NS = {
  'xlink:href': 'http://www.w3.org/1999/xlink',
  'xlink:title': 'http://www.w3.org/1999/xlink',
  'xml:lang': 'http://www.w3.org/XML/1998/namespace',
  'xml:space': 'http://www.w3.org/XML/1998/namespace',
};

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
      fetch(url, { method: 'POST', headers: { 'Content-Type': 'text/plain' }, body })
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
      fetch(url, { method: 'POST', headers: { 'Content-Type': 'text/plain' }, body })
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

// ─────────────────────────────────────────────────────────────────────
// Deep structural equality for Scott-encoded Agda values
// ─────────────────────────────────────────────────────────────────────

function deepEqual(a, b, depth) {
  if (a === b) return true;
  if (depth > 20) return false;  // guard against infinite recursion
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
 * Runs extract with each slot replaced; if output changes, binding depends on it.
 */
function detectSlots(extract, model, numSlots) {
  if (numSlots === 0) return null;
  const deps = [];
  let baseValue;
  try { baseValue = extract(model); } catch { return null; }
  for (let i = 0; i < numSlots; i++) {
    try {
      const modifiedValue = extract(replaceSlot(model, i));
      if (modifiedValue !== baseValue) deps.push(i);
    } catch {
      deps.push(i); // if it throws, assume dependency
    }
  }
  return deps.length > 0 ? deps : null;
}

/** Probe a Scott-encoded model, return its constructor args */
const _slotProbe = new Proxy({}, {
  get(_, name) { return (...args) => args; }
});

function probeSlots(model) {
  if (typeof model !== 'function') return null;
  try { return model(_slotProbe); } catch { return null; }
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
    numSlots: -1        // cached slot count (-1 = not yet detected)
  };
  if (parent) parent.children.push(scope);
  return scope;
}

function destroyScope(scope) {
  // Recursively destroy children
  for (const child of scope.children) {
    destroyScope(child);
  }
  // Remove from parent
  if (scope.parent) {
    const idx = scope.parent.children.indexOf(scope);
    if (idx !== -1) scope.parent.children.splice(idx, 1);
  }
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

  // Extract app, subs, cmd from module (mutable for hot reload)
  const appRecord = moduleExports.app;
  let subsFunc = moduleExports.subs || null;
  let cmdFunc = moduleExports.cmd || null;

  // Extract ReactiveApp fields (mutable for hot reload)
  const init = NodeModule.ReactiveApp.init(appRecord);
  let update = NodeModule.ReactiveApp.update(appRecord);
  let template = NodeModule.ReactiveApp.template(appRecord);

  // State
  let model = init;
  const rootScope = createScope(null);
  let currentScope = rootScope;
  let currentNs = null;  // null = HTML, SVG_NS, or MATHML_NS

  let currentSubscription = null;
  let currentEventFingerprint = null;
  let isUpdating = false;
  let pendingMessages = [];

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
      updateScope(rootScope, oldModel, model);

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
        updateScope(rootScope, nextOld, model);
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

        const attrArray = listToArray(attrs);
        for (const attr of attrArray) {
          applyAttr(el, attr);
        }

        const childArray = listToArray(children);
        for (const child of childArray) {
          const childNode = renderNode(child);
          if (childNode) el.appendChild(childNode);
        }

        currentNs = prevNs;  // restore after subtree
        return el;
      },

      empty: () => null,

      when: (cond, innerNode) => {
        const shouldShow = !!cond(model);

        if (shouldShow) {
          const childScope = createScope(currentScope);
          const rendered = withScope(childScope, () => renderNode(innerNode));
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
        const itemArray = listToArray(items);

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
        const itemArray = listToArray(items);

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

        currentScope.lists.push({
          marker, getList, render, renderedItems,
          keyed: true, keyFn
        });

        return container;
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
          dispatch(msg);
        });
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
            if (svg && svg.getScreenCTM) {
              const pt = svg.createSVGPoint();
              pt.x = e.clientX;
              pt.y = e.clientY;
              const svgPt = pt.matrixTransform(svg.getScreenCTM().inverse());
              value = svgPt.x + ',' + svgPt.y;
            } else {
              value = e.clientX + ',' + e.clientY;
            }
          } else {
            value = e.target.value || '';
          }
          dispatch(handler(value));
        });
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

  /**
   * Convert Agda list to JS array
   */
  function listToArray(list) {
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

  // ─────────────────────────────────────────────────────────────────
  // Scoped update
  // ─────────────────────────────────────────────────────────────────

  /**
   * Recursively update all bindings in a scope tree
   */
  function updateScope(scope, oldModel, newModel) {
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
        el.style.animation = 'none';
        requestAnimationFrame(() => { el.style.animation = val; });
      }
    }

    // Conditionals (when / whenT)
    for (const cond of scope.conditionals) {
      const showBool = !!cond.cond(newModel);

      if (showBool !== cond.rendered) {
        if (showBool) {
          // Show: render into new child scope
          const childScope = createScope(scope);
          const newNode = withScope(childScope, () => renderNode(cond.innerNode));

          // Enter transition
          if (cond.transition && newNode && newNode.classList) {
            newNode.classList.add(cond.transition.enterClass);
            requestAnimationFrame(() => {
              requestAnimationFrame(() => {
                if (newNode.classList) newNode.classList.remove(cond.transition.enterClass);
              });
            });
          }

          cond.node.replaceWith(newNode);
          cond.node = newNode;
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
            setTimeout(() => {
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
        updateScope(cond.scope, oldModel, newModel);
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

    // Recurse into child scopes (that aren't managed by conditionals/lists)
    // Note: conditional and list scopes are updated above, so children
    // array contains only "structural" children from elem nesting.
    // Actually, all child scopes are created by when/foreach, so
    // we don't need extra recursion here — it's handled above.
  }

  /**
   * Update unkeyed foreach list
   */
  function updateUnkeyedList(parentScope, list, oldModel, newModel) {
    const newItems = listToArray(list.getList(newModel));
    const oldItems = list.renderedItems;

    if (newItems.length !== oldItems.length) {
      // Length changed: destroy old scopes, rebuild
      for (const entry of oldItems) {
        entry.node.remove();
        if (entry.scope) destroyScope(entry.scope);
      }

      list.renderedItems = [];
      const parent = list.marker.parentNode;
      const insertBefore = list.marker.nextSibling;

      newItems.forEach((item, idx) => {
        const itemScope = createScope(parentScope);
        const itemNode = withScope(itemScope, () =>
          renderNode(list.render(item)(BigInt(idx)))
        );
        if (itemNode) {
          list.renderedItems.push({ item, node: itemNode, scope: itemScope });
          parent.insertBefore(itemNode, insertBefore);
        }
      });
    } else {
      // Same length: update bindings within each item's scope
      for (const entry of oldItems) {
        if (entry.scope) {
          updateScope(entry.scope, oldModel, newModel);
        }
      }
    }
  }

  /**
   * Update keyed foreach list — key-based reconciliation
   */
  function updateKeyedList(parentScope, list, oldModel, newModel) {
    const newItems = listToArray(list.getList(newModel));
    const oldItems = list.renderedItems;

    // Build old key map
    const oldKeyMap = new Map();
    for (let i = 0; i < oldItems.length; i++) {
      oldKeyMap.set(oldItems[i].key, oldItems[i]);
    }

    // Build new key set
    const newKeys = newItems.map(item => list.keyFn(item));

    // Check if anything changed
    const keysChanged = newKeys.length !== oldItems.length ||
      newKeys.some((key, i) => oldItems[i]?.key !== key);

    if (!keysChanged) {
      // Same keys in same order: just update bindings
      for (const entry of oldItems) {
        if (entry.scope) {
          updateScope(entry.scope, oldModel, newModel);
        }
      }
      return;
    }

    // Keys changed: reconcile
    const parent = list.marker.parentNode;
    const newRendered = [];
    const newKeySet = new Set(newKeys);

    // Remove items whose keys are no longer present
    for (const entry of oldItems) {
      if (!newKeySet.has(entry.key)) {
        entry.node.remove();
        if (entry.scope) destroyScope(entry.scope);
      }
    }

    // Build/reuse items in new order
    let insertBefore = list.marker.nextSibling;
    // First, remove all old items from DOM (we'll re-insert in order)
    for (const entry of oldItems) {
      if (newKeySet.has(entry.key) && entry.node.parentNode) {
        entry.node.remove();
      }
    }

    // Now insert in correct order
    insertBefore = list.marker.nextSibling;
    for (let i = 0; i < newItems.length; i++) {
      const key = newKeys[i];
      const oldEntry = oldKeyMap.get(key);

      if (oldEntry) {
        // Reuse existing DOM node
        parent.insertBefore(oldEntry.node, insertBefore);
        // Update bindings in existing scope
        if (oldEntry.scope) {
          updateScope(oldEntry.scope, oldModel, newModel);
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
        }
      }
    }

    list.renderedItems = newRendered;
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

    currentSubscription = interpretEvent(eventSpec, dispatch);
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
  }

  // Initial subscriptions
  updateSubscriptions();

  const counts = countBindings(rootScope);
  console.log(`Reactive app mounted: ${counts.text} text bindings, ${counts.attr} attr bindings, ${counts.style} style bindings`);

  // ─────────────────────────────────────────────────────────────────
  // Phase 8B: Big Lens — handle incoming peek/over WS messages
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
        console.log(`Big Lens: connected as ${bigLensClientId}`);
        return;
      }

      if (data.startsWith('peek:')) {
        // Server wants to read our model — respond with serialized model
        const serialized = JSON.stringify(model);
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
  // Phase 8 (polynomials.md): Time-Travel Debugging
  // ─────────────────────────────────────────────────────────────────

  let historyPast = [];      // previous models (newest first)
  let historyFuture = [];    // undone models (oldest first)
  const maxHistory = options.maxHistory || 100;

  function timeTravelDispatch(msg) {
    // Record current state before update
    historyPast.unshift(structuredClone ? structuredClone(model) : JSON.parse(JSON.stringify(model)));
    if (historyPast.length > maxHistory) historyPast.length = maxHistory;
    historyFuture = []; // new action clears redo
    dispatch(msg);
  }

  function timeTravel_undo() {
    if (historyPast.length === 0) return;
    const oldModel = model;
    historyFuture.unshift(structuredClone ? structuredClone(model) : JSON.parse(JSON.stringify(model)));
    model = historyPast.shift();
    updateScope(rootScope, oldModel, model);
    updateSubscriptions();
  }

  function timeTravel_redo() {
    if (historyFuture.length === 0) return;
    const oldModel = model;
    historyPast.unshift(structuredClone ? structuredClone(model) : JSON.parse(JSON.stringify(model)));
    model = historyFuture.shift();
    updateScope(rootScope, oldModel, model);
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
  // Phase 8 (polynomials.md): Hot Reload
  // ─────────────────────────────────────────────────────────────────

  function hotReload(newModuleExports) {
    const newAppRecord = newModuleExports.app;

    // Replace mutable function references
    update = NodeModule.ReactiveApp.update(newAppRecord);
    const newTemplate = NodeModule.ReactiveApp.template(newAppRecord);
    subsFunc = newModuleExports.subs || null;
    cmdFunc = newModuleExports.cmd || null;

    // Tear down old DOM
    if (currentSubscription) {
      unsubscribe(currentSubscription);
      currentSubscription = null;
      currentEventFingerprint = null;
    }
    destroyScope(rootScope);
    container.innerHTML = '';

    // Reset root scope
    Object.assign(rootScope, createScope(null));

    // Re-render with new template, preserving model
    template = newTemplate;
    const dom = renderNode(template);
    if (dom) container.appendChild(dom);

    // Re-subscribe
    updateSubscriptions();

    console.log('Hot reload complete — model preserved');
  }

  return {
    dispatch,
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
    destroy: () => {
      if (currentSubscription) {
        unsubscribe(currentSubscription);
      }
      if (bigLensWs) {
        bigLensWs.close();
      }
      destroyScope(rootScope);
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
