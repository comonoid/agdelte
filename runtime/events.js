/**
 * Agdelte Runtime - Event Subscriptions
 * Управление подписками на внешние события
 */

/**
 * Подписка на событие
 * @param {Object} eventSpec - Спецификация события
 * @param {Function} dispatch - Диспетчер сообщений
 * @returns {Object} - Объект подписки для отписки
 */
export function subscribe(eventSpec, dispatch) {
  const { type, config } = eventSpec;

  switch (type) {
    case 'interval':
      return subscribeInterval(config, dispatch);

    case 'animationFrame':
      return subscribeAnimationFrame(config, dispatch);

    case 'keyboard':
      return subscribeKeyboard(config, dispatch);

    case 'mouse':
      return subscribeMouse(config, dispatch);

    case 'resize':
      return subscribeResize(config, dispatch);

    case 'scroll':
      return subscribeScroll(config, dispatch);

    case 'visibility':
      return subscribeVisibility(config, dispatch);

    case 'online':
      return subscribeOnline(config, dispatch);

    case 'storage':
      return subscribeStorage(config, dispatch);

    case 'custom':
      return subscribeCustom(config, dispatch);

    default:
      console.warn(`Unknown event type: ${type}`);
      return { unsubscribe: () => {} };
  }
}

/**
 * Отписка от события
 */
export function unsubscribe(subscription) {
  if (subscription && typeof subscription.unsubscribe === 'function') {
    subscription.unsubscribe();
  }
}

/**
 * Diff подписок: какие удалить, какие добавить
 */
export function diffEvents(currentSubs, newEventSignal) {
  const removed = new Map();
  const added = new Map();

  // Извлекаем события из Signal (List EventSpec)
  const newSpecs = extractEventSpecs(newEventSignal);

  // Находим удалённые
  for (const [key, sub] of currentSubs) {
    if (!newSpecs.has(key)) {
      removed.set(key, sub);
    }
  }

  // Находим добавленные
  for (const [key, spec] of newSpecs) {
    if (!currentSubs.has(key)) {
      added.set(key, spec);
    }
  }

  return { removed, added };
}

/**
 * Извлечение спецификаций событий из Event сигнала
 */
function extractEventSpecs(eventSignal) {
  const specs = new Map();

  // Event = Signal (List EventSpec)
  // Проходим по структуре и извлекаем спецификации

  function extract(signal, depth = 0) {
    if (!signal || depth > 100) return; // Защита от бесконечности

    const events = signal.now;
    if (Array.isArray(events)) {
      for (const event of events) {
        if (event && event.type) {
          const key = eventKey(event);
          specs.set(key, event);
        }
      }
    }
  }

  extract(eventSignal);

  return specs;
}

/**
 * Уникальный ключ для события
 */
function eventKey(eventSpec) {
  const { type, config = {} } = eventSpec;
  return `${type}:${JSON.stringify(config)}`;
}

// ========================================
// Конкретные подписки
// ========================================

function subscribeInterval({ ms, msg }, dispatch) {
  const id = setInterval(() => {
    dispatch(msg);
  }, ms);

  return {
    type: 'interval',
    unsubscribe: () => clearInterval(id)
  };
}

function subscribeAnimationFrame({ msg }, dispatch) {
  let running = true;
  let frameId;

  function loop(timestamp) {
    if (!running) return;
    dispatch(typeof msg === 'function' ? msg(timestamp) : msg);
    frameId = requestAnimationFrame(loop);
  }

  frameId = requestAnimationFrame(loop);

  return {
    type: 'animationFrame',
    unsubscribe: () => {
      running = false;
      cancelAnimationFrame(frameId);
    }
  };
}

function subscribeKeyboard({ eventType = 'keydown', handler }, dispatch) {
  const listener = (e) => {
    const msg = handler({
      key: e.key,
      code: e.code,
      ctrl: e.ctrlKey,
      alt: e.altKey,
      shift: e.shiftKey,
      meta: e.metaKey
    });
    if (msg !== null && msg !== undefined) {
      dispatch(msg);
    }
  };

  document.addEventListener(eventType, listener);

  return {
    type: 'keyboard',
    unsubscribe: () => document.removeEventListener(eventType, listener)
  };
}

function subscribeMouse({ eventType = 'mousemove', handler }, dispatch) {
  const listener = (e) => {
    const msg = handler({
      x: e.clientX,
      y: e.clientY,
      pageX: e.pageX,
      pageY: e.pageY,
      button: e.button,
      buttons: e.buttons
    });
    if (msg !== null && msg !== undefined) {
      dispatch(msg);
    }
  };

  document.addEventListener(eventType, listener);

  return {
    type: 'mouse',
    unsubscribe: () => document.removeEventListener(eventType, listener)
  };
}

function subscribeResize({ handler }, dispatch) {
  const listener = () => {
    const msg = handler({
      width: window.innerWidth,
      height: window.innerHeight
    });
    dispatch(msg);
  };

  window.addEventListener('resize', listener);

  return {
    type: 'resize',
    unsubscribe: () => window.removeEventListener('resize', listener)
  };
}

function subscribeScroll({ handler }, dispatch) {
  const listener = () => {
    const msg = handler({
      x: window.scrollX,
      y: window.scrollY
    });
    dispatch(msg);
  };

  window.addEventListener('scroll', listener, { passive: true });

  return {
    type: 'scroll',
    unsubscribe: () => window.removeEventListener('scroll', listener)
  };
}

function subscribeVisibility({ handler }, dispatch) {
  const listener = () => {
    const msg = handler(document.visibilityState === 'visible');
    dispatch(msg);
  };

  document.addEventListener('visibilitychange', listener);

  return {
    type: 'visibility',
    unsubscribe: () => document.removeEventListener('visibilitychange', listener)
  };
}

function subscribeOnline({ onOnline, onOffline }, dispatch) {
  const onlineListener = () => dispatch(onOnline);
  const offlineListener = () => dispatch(onOffline);

  window.addEventListener('online', onlineListener);
  window.addEventListener('offline', offlineListener);

  return {
    type: 'online',
    unsubscribe: () => {
      window.removeEventListener('online', onlineListener);
      window.removeEventListener('offline', offlineListener);
    }
  };
}

function subscribeStorage({ key, handler }, dispatch) {
  const listener = (e) => {
    if (!key || e.key === key) {
      const msg = handler({
        key: e.key,
        oldValue: e.oldValue,
        newValue: e.newValue
      });
      dispatch(msg);
    }
  };

  window.addEventListener('storage', listener);

  return {
    type: 'storage',
    unsubscribe: () => window.removeEventListener('storage', listener)
  };
}

function subscribeCustom({ eventName, target = document, handler }, dispatch) {
  const listener = (e) => {
    const msg = handler(e.detail);
    dispatch(msg);
  };

  target.addEventListener(eventName, listener);

  return {
    type: 'custom',
    unsubscribe: () => target.removeEventListener(eventName, listener)
  };
}

// ========================================
// Утилиты для debounce/throttle
// ========================================

/**
 * Debounce: вызвать после паузы
 */
export function debounce(fn, ms) {
  let timeoutId;

  return (...args) => {
    clearTimeout(timeoutId);
    timeoutId = setTimeout(() => fn(...args), ms);
  };
}

/**
 * Throttle: вызывать не чаще чем раз в ms
 */
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

/**
 * Создание debounced подписки
 */
export function subscribeDebounced(eventSpec, dispatch, ms) {
  const debouncedDispatch = debounce(dispatch, ms);
  return subscribe(eventSpec, debouncedDispatch);
}

/**
 * Создание throttled подписки
 */
export function subscribeThrottled(eventSpec, dispatch, ms) {
  const throttledDispatch = throttle(dispatch, ms);
  return subscribe(eventSpec, throttledDispatch);
}
