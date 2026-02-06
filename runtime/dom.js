/**
 * Agdelte Runtime - Virtual DOM
 * DOM element creation and patching
 */

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
 * Convert Agda List to JavaScript Array
 * Agda List: [] = null or { head, tail } structure
 * Format may vary depending on compilation
 */
export function toArray(agdaList) {
  // If already an array — return as is
  if (Array.isArray(agdaList)) {
    return agdaList;
  }

  // If null/undefined — empty array
  if (agdaList == null) {
    return [];
  }

  // If Agda linked list: { head, tail } or { _1, _2 }
  const result = [];
  let current = agdaList;

  while (current != null) {
    // MAlonzo format: ["[]"] for empty, ["::", head, tail] for cons
    if (Array.isArray(current)) {
      if (current[0] === '[]' || current.length === 0) {
        break;
      }
      if (current[0] === '::' || current[0] === '_∷_') {
        result.push(current[1]);
        current = current[2];
        continue;
      }
    }

    // Format with head/tail fields
    if (current.head !== undefined) {
      result.push(current.head);
      current = current.tail;
      continue;
    }

    // Format with _1/_2 fields (old MAlonzo)
    if (current._1 !== undefined) {
      result.push(current._1);
      current = current._2;
      continue;
    }

    // Unrecognized format — possibly already a primitive
    break;
  }

  return result;
}

/**
 * Create real DOM from virtual DOM
 * @param {Object} vnode - Virtual node
 * @param {Function} dispatch - Message dispatcher
 * @param {string|null} ns - Current namespace (null = HTML, SVG_NS, MATHML_NS)
 * @returns {Node} - Real DOM node
 */
export function createElement(vnode, dispatch, ns = null) {
  if (vnode === null || vnode === undefined) {
    return document.createTextNode('');
  }

  // Text node
  if (vnode.tag === 'TEXT' || typeof vnode === 'string') {
    const text = typeof vnode === 'string' ? vnode : vnode.text;
    return document.createTextNode(text);
  }

  // Regular element: { tag, attrs, children }
  const { tag } = vnode;
  const attrs = toArray(vnode.attrs || []);
  const children = toArray(vnode.children || []);

  // Entering namespace
  if (tag === 'svg') ns = SVG_NS;
  else if (tag === 'math') ns = MATHML_NS;

  // Create element in current namespace
  const el = ns
    ? document.createElementNS(ns, tag)
    : document.createElement(tag);

  // Exiting namespace (children go back to HTML)
  const childNs = (tag === 'foreignObject' || tag === 'annotation-xml') ? null : ns;

  // Apply attributes
  for (const attr of attrs) {
    if (attr) applyAttribute(el, attr, dispatch);
  }

  // Create children
  if (vnode.keyed) {
    // Keyed children: [[key, vnode], ...] or Agda List of pairs
    for (const pair of children) {
      // pair can be [key, child] or { _1: key, _2: child }
      const key = Array.isArray(pair) ? pair[0] : (pair.fst || pair._1);
      const child = Array.isArray(pair) ? pair[1] : (pair.snd || pair._2);
      const childEl = createElement(child, dispatch, childNs);
      if (childEl.dataset) childEl.dataset.key = key;
      el.appendChild(childEl);
    }
  } else {
    for (const child of children) {
      el.appendChild(createElement(child, dispatch, childNs));
    }
  }

  return el;
}

/**
 * Set attribute with namespace support
 */
function setAttr(el, name, value) {
  const ns = ATTR_NS[name];
  if (ns) {
    el.setAttributeNS(ns, name, value);
  } else {
    el.setAttribute(name, value);
  }
}

/**
 * Apply attribute to element
 */
function applyAttribute(el, attr, dispatch) {
  const { type, name, value, handler } = attr;

  switch (type) {
    case 'attr':
      // Special handling for input value - must set property, not attribute
      if (name === 'value' && 'value' in el) {
        el.value = value;
      } else if (name === 'checked' && 'checked' in el) {
        el.checked = !!value;
      } else {
        setAttr(el, name, value);
      }
      break;

    case 'boolAttr':
      el.setAttribute(name, '');
      el[name] = true;
      break;

    case 'style':
      // Handle case where value contains multiple CSS properties
      // e.g., styles "background" "none; border: none; color: red"
      // Use setProperty for kebab-case CSS property names
      if (value && value.includes(';')) {
        // Set the first property by name
        const firstSemi = value.indexOf(';');
        el.style.setProperty(name, value.substring(0, firstSemi).trim());
        // Parse and apply remaining properties
        const remaining = value.substring(firstSemi + 1).trim();
        if (remaining) {
          for (const decl of remaining.split(';')) {
            const colonIdx = decl.indexOf(':');
            if (colonIdx > 0) {
              const prop = decl.substring(0, colonIdx).trim();
              const val = decl.substring(colonIdx + 1).trim();
              if (prop && val) el.style.setProperty(prop, val);
            }
          }
        }
      } else {
        el.style.setProperty(name, value);
      }
      break;

    case 'on':
      // Store handler in element, add listener only once
      el._handlers = el._handlers || {};
      el._handlers[`on:${name}`] = value;
      if (!el._listenersAttached?.[`on:${name}`]) {
        el._listenersAttached = el._listenersAttached || {};
        el._listenersAttached[`on:${name}`] = true;
        el.addEventListener(name, (e) => {
          const h = el._handlers[`on:${name}`];
          if (h) dispatch(h);
        });
      }
      break;

    case 'onPrevent':
      // Like 'on' but with preventDefault (for navigation links)
      el._handlers = el._handlers || {};
      el._handlers[`onPrevent:${name}`] = value;
      if (!el._listenersAttached?.[`onPrevent:${name}`]) {
        el._listenersAttached = el._listenersAttached || {};
        el._listenersAttached[`onPrevent:${name}`] = true;
        el.addEventListener(name, (e) => {
          e.preventDefault();
          const h = el._handlers[`onPrevent:${name}`];
          if (h) dispatch(h);
        });
      }
      break;

    case 'onInput':
      el._handlers = el._handlers || {};
      el._handlers['onInput'] = handler;
      if (!el._listenersAttached?.['onInput']) {
        el._listenersAttached = el._listenersAttached || {};
        el._listenersAttached['onInput'] = true;
        el.addEventListener('input', (e) => {
          const h = el._handlers['onInput'];
          if (h) dispatch(h(e.target.value));
        });
      }
      break;

    case 'onKey':
      el._handlers = el._handlers || {};
      el._handlers[`onKey:${name}`] = handler;
      if (!el._listenersAttached?.[`onKey:${name}`]) {
        el._listenersAttached = el._listenersAttached || {};
        el._listenersAttached[`onKey:${name}`] = true;
        el.addEventListener(name, (e) => {
          const h = el._handlers[`onKey:${name}`];
          if (h) dispatch(h(e.key));
        });
      }
      break;

    case 'key':
      el.dataset.key = value;
      break;

    default:
      // Fallback: regular attribute
      if (name && value !== undefined) {
        setAttr(el, name, value);
      }
  }
}

/**
 * Remove attribute
 */
function removeAttribute(el, attr) {
  const { type, name } = attr;

  switch (type) {
    case 'attr':
    case 'boolAttr':
      el.removeAttribute(name);
      if (name in el) {
        el[name] = false;
      }
      break;

    case 'style':
      el.style.removeProperty(name);
      break;

    case 'on':
    case 'onInput':
    case 'onKey':
      // Event handlers are removed when element is replaced
      break;

    case 'key':
      delete el.dataset.key;
      break;
  }
}

/**
 * Detect namespace from vnode tag
 */
function detectNs(vnode, parentNs) {
  if (!vnode || typeof vnode === 'string' || vnode.tag === 'TEXT') return parentNs;
  const tag = vnode.tag;
  if (tag === 'svg') return SVG_NS;
  if (tag === 'math') return MATHML_NS;
  if (tag === 'foreignObject' || tag === 'annotation-xml') return null;
  return parentNs;
}

/**
 * DOM patching: apply diff between old and new VDOM
 * @param {Node} dom - Current DOM node
 * @param {Object} oldVnode - Old virtual node
 * @param {Object} newVnode - New virtual node
 * @param {Function} dispatch - Dispatcher
 * @param {string|null} ns - Current namespace
 * @returns {Node} - Updated DOM node
 */
export function patch(dom, oldVnode, newVnode, dispatch, ns = null) {
  // If nodes are identical — do nothing
  if (oldVnode === newVnode) {
    return dom;
  }

  // If new node is null — remove
  if (newVnode === null || newVnode === undefined) {
    dom.parentNode?.removeChild(dom);
    return null;
  }

  // If old node is null — create new
  if (oldVnode === null || oldVnode === undefined) {
    return createElement(newVnode, dispatch, ns);
  }

  // If types differ — full replacement
  if (getNodeType(oldVnode) !== getNodeType(newVnode)) {
    const newDom = createElement(newVnode, dispatch, ns);
    dom.parentNode?.replaceChild(newDom, dom);
    return newDom;
  }

  // Text nodes
  if (isTextNode(newVnode)) {
    const newText = typeof newVnode === 'string' ? newVnode : newVnode.text;
    const oldText = typeof oldVnode === 'string' ? oldVnode : oldVnode.text;

    if (newText !== oldText) {
      dom.textContent = newText;
    }
    return dom;
  }

  // Different tags — replace
  if (oldVnode.tag !== newVnode.tag) {
    const newNs = detectNs(newVnode, ns);
    const newDom = createElement(newVnode, dispatch, newNs);
    dom.parentNode?.replaceChild(newDom, dom);
    return newDom;
  }

  // Same tag — patch attributes and children
  const childNs = detectNs(newVnode, ns);
  patchAttributes(dom, toArray(oldVnode.attrs || []), toArray(newVnode.attrs || []), dispatch);
  patchChildren(dom, oldVnode, newVnode, dispatch, childNs);

  return dom;
}

/**
 * Patch attributes
 * Now handles events efficiently - updates handler reference without recreating element
 */
function patchAttributes(el, oldAttrs, newAttrs, dispatch) {
  const oldMap = new Map(oldAttrs.filter(Boolean).map(a => [attrKey(a), a]));
  const newMap = new Map(newAttrs.filter(Boolean).map(a => [attrKey(a), a]));

  // Remove old
  for (const [key, attr] of oldMap) {
    if (!newMap.has(key)) {
      removeAttribute(el, attr);
    }
  }

  // Add/update new (including events - now updated efficiently)
  for (const [key, attr] of newMap) {
    const oldAttr = oldMap.get(key);
    if (!oldAttr || !attrsEqual(oldAttr, attr)) {
      applyAttribute(el, attr, dispatch);
    }
  }
}

/**
 * Patch children
 */
function patchChildren(el, oldVnode, newVnode, dispatch, ns = null) {
  const oldChildren = toArray(oldVnode.children || []);
  const newChildren = toArray(newVnode.children || []);

  // Keyed diffing
  if (newVnode.keyed && oldVnode.keyed) {
    patchKeyedChildren(el, oldChildren, newChildren, dispatch, ns);
    return;
  }

  // Simple diffing
  const maxLen = Math.max(oldChildren.length, newChildren.length);

  for (let i = 0; i < maxLen; i++) {
    const oldChild = oldChildren[i];
    const newChild = newChildren[i];

    if (i >= oldChildren.length) {
      // Add new
      el.appendChild(createElement(newChild, dispatch, ns));
    } else if (i >= newChildren.length) {
      // Remove extra
      el.removeChild(el.childNodes[newChildren.length]);
    } else {
      // Patch existing
      patch(el.childNodes[i], oldChild, newChild, dispatch, ns);
    }
  }
}

/**
 * Patch keyed children (efficient diffing)
 */
function patchKeyedChildren(el, oldChildren, newChildren, dispatch, ns = null) {
  const oldMap = new Map(oldChildren);
  const newMap = new Map(newChildren);

  // Remove elements that no longer exist
  for (const [key] of oldChildren) {
    if (!newMap.has(key)) {
      const toRemove = el.querySelector(`[data-key="${key}"]`);
      if (toRemove) {
        el.removeChild(toRemove);
      }
    }
  }

  // Add/update/move
  let prevDom = null;

  for (const [key, newChild] of newChildren) {
    const oldChild = oldMap.get(key);
    let dom = el.querySelector(`[data-key="${key}"]`);

    if (!oldChild) {
      // New element
      dom = createElement(newChild, dispatch, ns);
      dom.dataset.key = key;

      if (prevDom) {
        prevDom.after(dom);
      } else {
        el.prepend(dom);
      }
    } else {
      // Update existing
      dom = patch(dom, oldChild, newChild, dispatch, ns);

      // Move if needed
      if (prevDom && prevDom.nextSibling !== dom) {
        prevDom.after(dom);
      } else if (!prevDom && el.firstChild !== dom) {
        el.prepend(dom);
      }
    }

    prevDom = dom;
  }
}

/**
 * Utilities
 */
function getNodeType(vnode) {
  if (typeof vnode === 'string') return 'text';
  if (vnode.tag === 'TEXT') return 'text';
  return 'element';
}

function isTextNode(vnode) {
  return typeof vnode === 'string' || vnode.tag === 'TEXT';
}

function attrKey(attr) {
  return `${attr.type}:${attr.name}`;
}

function attrsEqual(a, b) {
  return a.type === b.type &&
         a.name === b.name &&
         a.value === b.value;
}

/**
 * Render VDOM to HTML string (for SSR)
 */
export function renderToString(vnode) {
  if (vnode === null || vnode === undefined) {
    return '';
  }

  if (typeof vnode === 'string') {
    return escapeHtml(vnode);
  }

  if (vnode.tag === 'TEXT') {
    return escapeHtml(vnode.text);
  }

  const { tag } = vnode;
  const attrs = toArray(vnode.attrs || []);
  const children = toArray(vnode.children || []);

  // Self-closing tags
  const selfClosing = ['br', 'hr', 'img', 'input', 'meta', 'link'];

  let html = `<${tag}`;

  // Attributes
  for (const attr of attrs) {
    if (!attr) continue;
    if (attr.type === 'attr') {
      html += ` ${attr.name}="${escapeHtml(attr.value)}"`;
    } else if (attr.type === 'boolAttr') {
      html += ` ${attr.name}`;
    } else if (attr.type === 'style') {
      // Handle case where value contains multiple CSS properties
      if (attr.value && attr.value.includes(';')) {
        const firstSemi = attr.value.indexOf(';');
        let styleStr = `${attr.name}: ${attr.value.substring(0, firstSemi).trim()}`;
        const remaining = attr.value.substring(firstSemi + 1).trim();
        if (remaining) styleStr += '; ' + remaining;
        html += ` style="${escapeHtml(styleStr)}"`;
      } else {
        html += ` style="${attr.name}: ${escapeHtml(attr.value)}"`;
      }
    }
    // Events are not rendered to HTML
  }

  if (selfClosing.includes(tag)) {
    return html + ' />';
  }

  html += '>';

  // Children
  if (vnode.keyed) {
    for (const [, child] of children) {
      html += renderToString(child);
    }
  } else {
    for (const child of children) {
      html += renderToString(child);
    }
  }

  html += `</${tag}>`;

  return html;
}

function escapeHtml(str) {
  return String(str)
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
    .replace(/'/g, '&#039;');
}
