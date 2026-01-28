/**
 * Agdelte Runtime - Virtual DOM
 * Создание и патчинг DOM элементов
 */

/**
 * Конвертация Agda List в JavaScript Array
 * Agda List: [] = null или { head, tail } структура
 * В зависимости от компиляции может быть разный формат
 */
function toArray(agdaList) {
  // Если уже массив — возвращаем как есть
  if (Array.isArray(agdaList)) {
    return agdaList;
  }

  // Если null/undefined — пустой массив
  if (agdaList == null) {
    return [];
  }

  // Если это Agda linked list: { head, tail } или { _1, _2 }
  const result = [];
  let current = agdaList;

  while (current != null) {
    // Формат MAlonzo: ["[]"] для пустого, ["::", head, tail] для cons
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

    // Формат с полями head/tail
    if (current.head !== undefined) {
      result.push(current.head);
      current = current.tail;
      continue;
    }

    // Формат с полями _1/_2 (старый MAlonzo)
    if (current._1 !== undefined) {
      result.push(current._1);
      current = current._2;
      continue;
    }

    // Не распознали формат — возможно уже примитив
    break;
  }

  return result;
}

/**
 * Создание реального DOM из виртуального
 * @param {Object} vnode - Виртуальный узел
 * @param {Function} dispatch - Диспетчер сообщений
 * @returns {Node} - Реальный DOM узел
 */
export function createElement(vnode, dispatch) {
  if (vnode === null || vnode === undefined) {
    return document.createTextNode('');
  }

  // Текстовый узел
  if (vnode.tag === 'TEXT' || typeof vnode === 'string') {
    const text = typeof vnode === 'string' ? vnode : vnode.text;
    return document.createTextNode(text);
  }

  // Обычный элемент: { tag, attrs, children }
  const { tag } = vnode;
  const attrs = toArray(vnode.attrs || []);
  const children = toArray(vnode.children || []);

  // Создаём элемент
  const el = document.createElement(tag);

  // Применяем атрибуты
  for (const attr of attrs) {
    if (attr) applyAttribute(el, attr, dispatch);
  }

  // Создаём детей
  if (vnode.keyed) {
    // Keyed children: [[key, vnode], ...] или Agda List of pairs
    for (const pair of children) {
      // pair может быть [key, child] или { _1: key, _2: child }
      const key = Array.isArray(pair) ? pair[0] : (pair.fst || pair._1);
      const child = Array.isArray(pair) ? pair[1] : (pair.snd || pair._2);
      const childEl = createElement(child, dispatch);
      if (childEl.dataset) childEl.dataset.key = key;
      el.appendChild(childEl);
    }
  } else {
    for (const child of children) {
      el.appendChild(createElement(child, dispatch));
    }
  }

  return el;
}

/**
 * Применение атрибута к элементу
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
        el.setAttribute(name, value);
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
      // Fallback: обычный атрибут
      if (name && value !== undefined) {
        el.setAttribute(name, value);
      }
  }
}

/**
 * Удаление атрибута
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
      // Обработчики событий удаляются при замене элемента
      break;

    case 'key':
      delete el.dataset.key;
      break;
  }
}

/**
 * Патчинг DOM: применение разницы между старым и новым VDOM
 * @param {Node} dom - Текущий DOM узел
 * @param {Object} oldVnode - Старый виртуальный узел
 * @param {Object} newVnode - Новый виртуальный узел
 * @param {Function} dispatch - Диспетчер
 * @returns {Node} - Обновлённый DOM узел
 */
export function patch(dom, oldVnode, newVnode, dispatch) {
  // Если узлы идентичны — ничего не делаем
  if (oldVnode === newVnode) {
    return dom;
  }

  // Если новый узел null — удаляем
  if (newVnode === null || newVnode === undefined) {
    dom.parentNode?.removeChild(dom);
    return null;
  }

  // Если старый узел null — создаём новый
  if (oldVnode === null || oldVnode === undefined) {
    return createElement(newVnode, dispatch);
  }

  // Если типы разные — полная замена
  if (getNodeType(oldVnode) !== getNodeType(newVnode)) {
    const newDom = createElement(newVnode, dispatch);
    dom.parentNode?.replaceChild(newDom, dom);
    return newDom;
  }

  // Текстовые узлы
  if (isTextNode(newVnode)) {
    const newText = typeof newVnode === 'string' ? newVnode : newVnode.text;
    const oldText = typeof oldVnode === 'string' ? oldVnode : oldVnode.text;

    if (newText !== oldText) {
      dom.textContent = newText;
    }
    return dom;
  }

  // Разные теги — замена
  if (oldVnode.tag !== newVnode.tag) {
    const newDom = createElement(newVnode, dispatch);
    dom.parentNode?.replaceChild(newDom, dom);
    return newDom;
  }

  // Тот же тег — патчим атрибуты и детей
  patchAttributes(dom, toArray(oldVnode.attrs || []), toArray(newVnode.attrs || []), dispatch);
  patchChildren(dom, oldVnode, newVnode, dispatch);

  return dom;
}

/**
 * Патчинг атрибутов
 * Now handles events efficiently - updates handler reference without recreating element
 */
function patchAttributes(el, oldAttrs, newAttrs, dispatch) {
  const oldMap = new Map(oldAttrs.filter(Boolean).map(a => [attrKey(a), a]));
  const newMap = new Map(newAttrs.filter(Boolean).map(a => [attrKey(a), a]));

  // Удаляем старые
  for (const [key, attr] of oldMap) {
    if (!newMap.has(key)) {
      removeAttribute(el, attr);
    }
  }

  // Добавляем/обновляем новые (включая events - теперь они обновляются эффективно)
  for (const [key, attr] of newMap) {
    const oldAttr = oldMap.get(key);
    if (!oldAttr || !attrsEqual(oldAttr, attr)) {
      applyAttribute(el, attr, dispatch);
    }
  }
}

/**
 * Патчинг детей
 */
function patchChildren(el, oldVnode, newVnode, dispatch) {
  const oldChildren = toArray(oldVnode.children || []);
  const newChildren = toArray(newVnode.children || []);

  // Keyed diffing
  if (newVnode.keyed && oldVnode.keyed) {
    patchKeyedChildren(el, oldChildren, newChildren, dispatch);
    return;
  }

  // Simple diffing
  const maxLen = Math.max(oldChildren.length, newChildren.length);

  for (let i = 0; i < maxLen; i++) {
    const oldChild = oldChildren[i];
    const newChild = newChildren[i];

    if (i >= oldChildren.length) {
      // Добавляем новый
      el.appendChild(createElement(newChild, dispatch));
    } else if (i >= newChildren.length) {
      // Удаляем лишний
      el.removeChild(el.childNodes[newChildren.length]);
    } else {
      // Патчим существующий
      patch(el.childNodes[i], oldChild, newChild, dispatch);
    }
  }
}

/**
 * Патчинг keyed детей (эффективный diffing)
 */
function patchKeyedChildren(el, oldChildren, newChildren, dispatch) {
  const oldMap = new Map(oldChildren);
  const newMap = new Map(newChildren);

  // Удаляем элементы которых больше нет
  for (const [key] of oldChildren) {
    if (!newMap.has(key)) {
      const toRemove = el.querySelector(`[data-key="${key}"]`);
      if (toRemove) {
        el.removeChild(toRemove);
      }
    }
  }

  // Добавляем/обновляем/перемещаем
  let prevDom = null;

  for (const [key, newChild] of newChildren) {
    const oldChild = oldMap.get(key);
    let dom = el.querySelector(`[data-key="${key}"]`);

    if (!oldChild) {
      // Новый элемент
      dom = createElement(newChild, dispatch);
      dom.dataset.key = key;

      if (prevDom) {
        prevDom.after(dom);
      } else {
        el.prepend(dom);
      }
    } else {
      // Обновляем существующий
      dom = patch(dom, oldChild, newChild, dispatch);

      // Перемещаем если нужно
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
 * Утилиты
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
 * Рендеринг VDOM в HTML строку (для SSR)
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

  // Атрибуты
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
    // События не рендерим в HTML
  }

  if (selfClosing.includes(tag)) {
    return html + ' />';
  }

  html += '>';

  // Дети
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
