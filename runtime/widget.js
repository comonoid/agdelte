/**
 * Agdelte Widget Runtime - No Virtual DOM!
 *
 * This runtime implements the Widget Lens approach:
 * - No Virtual DOM diffing
 * - Direct DOM mutations computed from model changes
 * - Widget.diff(oldModel, newModel) returns exactly which paths to mutate
 *
 * Key insight: Virtual DOM does diff(view(old), view(new))
 * Widget Lenses do: applyMutations(widget.diff(old, new))
 *
 * The Widget knows HOW to update, not just WHAT to show.
 */

import { toArray } from './dom.js';

/**
 * Navigate to a DOM node via Path
 * Path structure:
 * - here: current node
 * - child(n, p): go to nth child, then follow p
 * - text: get text content target
 * - attr(name): get attribute target
 */
function navigatePath(root, path) {
  // Scott-encoded Path pattern matching
  return path({
    here: () => ({ node: root, type: 'node' }),

    child: (n, subpath) => {
      const nNum = typeof n === 'bigint' ? Number(n) : n;
      const child = root.children[nNum];
      if (!child) {
        console.warn(`Widget: no child at index ${nNum}`);
        return null;
      }
      return navigatePath(child, subpath);
    },

    text: () => ({ node: root, type: 'text' }),

    attr: (name) => ({ node: root, type: 'attr', name })
  });
}

/**
 * Apply a single mutation at a path target
 */
function applyMutation(target, mutation) {
  if (!target) return;

  const { node, type, name } = target;

  // Scott-encoded Mutation pattern matching
  mutation({
    setText: (text) => {
      if (type === 'text') {
        node.textContent = text;
      } else if (type === 'node') {
        node.textContent = text;
      }
    },

    setAttr: (attrName, value) => {
      node.setAttribute(attrName, value);
    },

    remove: () => {
      node.parentNode?.removeChild(node);
    }
  });
}

/**
 * Apply a list of (Path, Mutation) pairs to the DOM
 */
function applyMutations(root, mutations) {
  const mutationList = toArray(mutations);

  for (const pair of mutationList) {
    // Pair might be { _1, _2 } or [path, mutation]
    const path = pair._1 || pair[0] || pair.fst;
    const mutation = pair._2 || pair[1] || pair.snd;

    if (path && mutation) {
      const target = navigatePath(root, path);
      applyMutation(target, mutation);
    }
  }
}

/**
 * Setup event handlers from Widget.handlers
 * handlers: List (Path × String × (String → Msg))
 */
function setupHandlers(root, handlers, dispatch) {
  const handlerList = toArray(handlers);

  for (const handler of handlerList) {
    // Triple: (path, eventName, handlerFn)
    const path = handler._1 || handler[0];
    const eventName = handler._2?._1 || handler[1];
    const handlerFn = handler._2?._2 || handler[2];

    if (path && eventName && handlerFn) {
      const target = navigatePath(root, path);
      if (target && target.node) {
        target.node.addEventListener(eventName, (e) => {
          const msg = handlerFn(e.target?.value || '');
          dispatch(msg);
        });
      }
    }
  }
}

/**
 * Run a WidgetApp
 *
 * @param {Object} widgetApp - Compiled WidgetApp with init, update, widget fields
 * @param {HTMLElement} container - DOM container
 * @param {HTMLElement} template - Pre-rendered HTML template for initial structure
 * @returns {Object} App instance
 */
export function runWidgetApp(widgetApp, container, template) {
  // Extract fields from Scott-encoded record
  const init = widgetApp["record"]({"record": (i, u, w) => i});
  const update = widgetApp["record"]({"record": (i, u, w) => u});
  const widget = widgetApp["record"]({"record": (i, u, w) => w});

  // Extract widget fields
  const widgetTemplate = widget["record"]({"record": (t, d, h) => t});
  const widgetDiff = widget["record"]({"record": (t, d, h) => d});
  const widgetHandlers = widget["record"]({"record": (t, d, h) => h});

  // Current model state
  let model = init;

  // Mount template if provided, otherwise use container's existing content
  let root = container.firstElementChild;
  if (template) {
    container.innerHTML = '';
    container.appendChild(template.cloneNode(true));
    root = container.firstElementChild;
  }

  if (!root) {
    console.error('Widget: no root element found. Provide a template or pre-render HTML.');
    return null;
  }

  // Dispatch function
  function dispatch(msg) {
    const oldModel = model;
    model = update(msg)(oldModel);

    // Compute and apply mutations - no diffing!
    const mutations = widgetDiff(oldModel)(model);
    applyMutations(root, mutations);
  }

  // Setup event handlers
  setupHandlers(root, widgetHandlers, dispatch);

  // Apply initial values from template spec
  const templatePairs = toArray(widgetTemplate);
  for (const pair of templatePairs) {
    const path = pair._1 || pair[0] || pair.fst;
    const value = pair._2 || pair[1] || pair.snd;

    if (path && value) {
      const target = navigatePath(root, path);
      if (target) {
        if (target.type === 'text') {
          target.node.textContent = value;
        } else if (target.type === 'attr') {
          target.node.setAttribute(target.name, value);
        }
      }
    }
  }

  return {
    dispatch,
    getModel: () => model,
    getRoot: () => root
  };
}

/**
 * Mount a WidgetApp with HTML template
 *
 * @param {Object} widgetApp - Compiled WidgetApp
 * @param {string} selector - Container selector
 * @param {string} templateHTML - HTML string for initial structure
 * @returns {Object} App instance
 *
 * @example
 * // Counter template: button(-), span(count), button(+)
 * const template = `
 *   <div class="counter">
 *     <button>-</button>
 *     <span>0</span>
 *     <button>+</button>
 *   </div>
 * `;
 * mountWidget(counterApp, '#app', template);
 */
export function mountWidget(widgetApp, selector, templateHTML) {
  const container = document.querySelector(selector);
  if (!container) {
    throw new Error(`Widget: container not found: ${selector}`);
  }

  // Parse template
  const templateDiv = document.createElement('div');
  templateDiv.innerHTML = templateHTML.trim();
  const template = templateDiv.firstElementChild;

  return runWidgetApp(widgetApp, container, template);
}

export { applyMutations, navigatePath, setupHandlers };
