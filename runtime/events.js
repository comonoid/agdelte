/**
 * Agdelte Runtime - Event Interpreter
 *
 * Event теперь data type (AST), а не Signal.
 * Runtime интерпретирует этот AST и создаёт подписки.
 *
 * Scott encoding:
 *   Event.never     = cb => cb.never()
 *   Event.interval  = ms => msg => cb => cb.interval(ms, msg)
 *   Event.merge     = e1 => e2 => cb => cb.merge(e1, e2)
 */

// WebSocket connections pool (shared with commands)
export const wsConnections = new Map();

/**
 * Создаёт WsMsg (Scott-encoded)
 */
function mkWsMsg(tag, value) {
  return (cb) => {
    switch (tag) {
      case 'WsConnected': return cb.WsConnected();
      case 'WsMessage': return cb.WsMessage(value);
      case 'WsClosed': return cb.WsClosed();
      case 'WsError': return cb.WsError(value);
    }
  };
}

/**
 * Интерпретирует Event AST и создаёт подписки
 * @param {Object} event - Event (Scott-encoded)
 * @param {Function} dispatch - Диспетчер сообщений
 * @returns {Object} - { unsubscribe: () => void }
 */
export function interpretEvent(event, dispatch) {
  if (!event) {
    return { unsubscribe: () => {} };
  }

  // Scott encoding: вызываем event с объектом обработчиков
  return event({
    // never: ничего не делаем
    never: () => ({ unsubscribe: () => {} }),

    // interval: периодическое событие
    interval: (ms, msg) => {
      const msNum = typeof ms === 'bigint' ? Number(ms) : ms;
      const id = setInterval(() => dispatch(msg), msNum);
      return { unsubscribe: () => clearInterval(id) };
    },

    // timeout: однократное событие
    timeout: (ms, msg) => {
      const msNum = typeof ms === 'bigint' ? Number(ms) : ms;
      const id = setTimeout(() => dispatch(msg), msNum);
      return { unsubscribe: () => clearTimeout(id) };
    },

    // onKeyDown: клавиатура (keydown)
    onKeyDown: (handler) => {
      const listener = (e) => {
        const keyEvent = mkKeyboardEvent(e);
        const maybeMsg = handler(keyEvent);
        const msg = extractMaybe(maybeMsg);
        if (msg !== null) {
          dispatch(msg);
        }
      };
      document.addEventListener('keydown', listener);
      return { unsubscribe: () => document.removeEventListener('keydown', listener) };
    },

    // onKeyUp: клавиатура (keyup)
    onKeyUp: (handler) => {
      const listener = (e) => {
        const keyEvent = mkKeyboardEvent(e);
        const maybeMsg = handler(keyEvent);
        const msg = extractMaybe(maybeMsg);
        if (msg !== null) {
          dispatch(msg);
        }
      };
      document.addEventListener('keyup', listener);
      return { unsubscribe: () => document.removeEventListener('keyup', listener) };
    },

    // httpGet: HTTP GET запрос
    httpGet: (url, onSuccess, onError) => {
      const controller = new AbortController();
      let completed = false;

      fetch(url, { signal: controller.signal })
        .then(async (response) => {
          if (completed) return;
          if (!response.ok) {
            throw new Error(`HTTP ${response.status}: ${response.statusText}`);
          }
          const text = await response.text();
          completed = true;
          dispatch(onSuccess(text));
        })
        .catch((error) => {
          if (completed || error.name === 'AbortError') return;
          completed = true;
          dispatch(onError(error.message));
        });

      return {
        unsubscribe: () => {
          if (!completed) controller.abort();
        }
      };
    },

    // httpPost: HTTP POST запрос
    httpPost: (url, body, onSuccess, onError) => {
      const controller = new AbortController();
      let completed = false;

      fetch(url, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body,
        signal: controller.signal
      })
        .then(async (response) => {
          if (completed) return;
          if (!response.ok) {
            throw new Error(`HTTP ${response.status}: ${response.statusText}`);
          }
          const text = await response.text();
          completed = true;
          dispatch(onSuccess(text));
        })
        .catch((error) => {
          if (completed || error.name === 'AbortError') return;
          completed = true;
          dispatch(onError(error.message));
        });

      return {
        unsubscribe: () => {
          if (!completed) controller.abort();
        }
      };
    },

    // merge: объединение двух событий
    merge: (e1, e2) => {
      const sub1 = interpretEvent(e1, dispatch);
      const sub2 = interpretEvent(e2, dispatch);
      return {
        unsubscribe: () => {
          sub1.unsubscribe();
          sub2.unsubscribe();
        }
      };
    },

    // debounce: задержка после паузы
    debounce: (ms, innerEvent) => {
      const msNum = typeof ms === 'bigint' ? Number(ms) : ms;
      let timeoutId = null;
      let lastMsg = null;

      const debouncedDispatch = (msg) => {
        lastMsg = msg;
        if (timeoutId) clearTimeout(timeoutId);
        timeoutId = setTimeout(() => {
          dispatch(lastMsg);
          timeoutId = null;
        }, msNum);
      };

      const sub = interpretEvent(innerEvent, debouncedDispatch);
      return {
        unsubscribe: () => {
          if (timeoutId) clearTimeout(timeoutId);
          sub.unsubscribe();
        }
      };
    },

    // throttle: ограничение частоты
    throttle: (ms, innerEvent) => {
      const msNum = typeof ms === 'bigint' ? Number(ms) : ms;
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
          dispatch(msg);
        } else {
          pendingMsg = msg;
          if (!timeoutId) {
            timeoutId = setTimeout(() => {
              lastCall = Date.now();
              timeoutId = null;
              if (pendingMsg !== null) {
                dispatch(pendingMsg);
                pendingMsg = null;
              }
            }, remaining);
          }
        }
      };

      const sub = interpretEvent(innerEvent, throttledDispatch);
      return {
        unsubscribe: () => {
          if (timeoutId) clearTimeout(timeoutId);
          sub.unsubscribe();
        }
      };
    },

    // wsConnect: WebSocket соединение
    wsConnect: (url, handler) => {
      const ws = new WebSocket(url);

      ws.onopen = () => {
        dispatch(handler(mkWsMsg('WsConnected')));
      };

      ws.onmessage = (e) => {
        dispatch(handler(mkWsMsg('WsMessage', e.data)));
      };

      ws.onerror = (e) => {
        dispatch(handler(mkWsMsg('WsError', e.message || 'Unknown error')));
      };

      ws.onclose = () => {
        dispatch(handler(mkWsMsg('WsClosed')));
      };

      // Регистрируем для wsSend
      wsConnections.set(url, ws);

      return {
        unsubscribe: () => {
          wsConnections.delete(url);
          if (ws.readyState === WebSocket.OPEN || ws.readyState === WebSocket.CONNECTING) {
            ws.close();
          }
        }
      };
    },

    // foldE: accumulate state across event occurrences
    // Scott: foldE(_typeB, init, step, innerEvent)
    foldE: (_typeB, init, step, innerEvent) => {
      let state = init;
      const wrappedDispatch = (inputVal) => {
        state = step(inputVal)(state);
        dispatch(state);
      };
      const sub = interpretEvent(innerEvent, wrappedDispatch);
      return {
        unsubscribe: () => sub.unsubscribe()
      };
    },

    // mapFilterE: map + filter via Maybe
    // Scott: mapFilterE(_typeB, f, innerEvent)
    mapFilterE: (_typeB, f, innerEvent) => {
      const wrappedDispatch = (inputVal) => {
        const maybeResult = f(inputVal);
        // Extract Maybe: just(x) → dispatch(x), nothing → skip
        if (maybeResult) {
          const result = maybeResult({
            just: (x) => x,
            nothing: () => null
          });
          if (result !== null) dispatch(result);
        }
      };
      const sub = interpretEvent(innerEvent, wrappedDispatch);
      return {
        unsubscribe: () => sub.unsubscribe()
      };
    },

    // switchE: start with initial event, switch on meta-event
    // Scott: switchE(initialEvent, metaEvent)
    switchE: (initialEvent, metaEvent) => {
      let currentSub = interpretEvent(initialEvent, dispatch);

      const metaDispatch = (newEvent) => {
        // Unsubscribe from current, switch to new
        currentSub.unsubscribe();
        currentSub = interpretEvent(newEvent, dispatch);
      };

      const metaSub = interpretEvent(metaEvent, metaDispatch);

      return {
        unsubscribe: () => {
          currentSub.unsubscribe();
          metaSub.unsubscribe();
        }
      };
    },

    // worker: Web Worker (structured concurrency — terminate on unsubscribe)
    worker: (scriptUrl, input, onResult, onError) => {
      let w;
      try {
        w = new Worker(scriptUrl, { type: 'module' });
      } catch (e) {
        dispatch(onError(e.message || 'Failed to create worker'));
        return { unsubscribe: () => {} };
      }

      w.onmessage = (e) => {
        dispatch(onResult(typeof e.data === 'string' ? e.data : JSON.stringify(e.data)));
      };

      w.onerror = (e) => {
        dispatch(onError(e.message || 'Worker error'));
      };

      // Send input to worker
      w.postMessage(input);

      return {
        unsubscribe: () => {
          w.terminate();
        }
      };
    },

    // onUrlChange: изменение URL (popstate)
    onUrlChange: (handler) => {
      const listener = () => {
        dispatch(handler(window.location.pathname + window.location.search));
      };

      window.addEventListener('popstate', listener);

      return {
        unsubscribe: () => window.removeEventListener('popstate', listener)
      };
    }
  });
}

/**
 * Создаёт KeyboardEvent record для Agda (Scott-encoded)
 * Agda record = { constructorName: cb => cb.constructorName(fields...) }
 */
function mkKeyboardEvent(e) {
  return {
    mkKeyboardEvent: (cb) => cb.mkKeyboardEvent(
      e.key,
      e.code,
      e.ctrlKey,
      e.altKey,
      e.shiftKey,
      e.metaKey
    )
  };
}

/**
 * Извлекает значение из Maybe (Scott-encoded)
 * Maybe.just(x)  = cb => cb.just(x)
 * Maybe.nothing  = cb => cb.nothing()
 */
function extractMaybe(maybe) {
  if (!maybe) return null;
  return maybe({
    just: (x) => x,
    nothing: () => null
  });
}

/**
 * Legacy: подписка на событие (для совместимости)
 */
export function subscribe(eventSpec, dispatch) {
  // Если это старый формат (plain object), используем старую логику
  if (eventSpec && eventSpec.type) {
    return subscribeLegacy(eventSpec, dispatch);
  }
  // Иначе интерпретируем как Event AST
  return interpretEvent(eventSpec, dispatch);
}

/**
 * Legacy подписка для старого формата {type, config}
 */
function subscribeLegacy(eventSpec, dispatch) {
  const { type, config } = eventSpec;

  switch (type) {
    case 'never':
      return { unsubscribe: () => {} };

    case 'interval': {
      const msNum = typeof config.ms === 'bigint' ? Number(config.ms) : config.ms;
      const id = setInterval(() => dispatch(config.msg), msNum);
      return { unsubscribe: () => clearInterval(id) };
    }

    case 'timeout': {
      const msNum = typeof config.ms === 'bigint' ? Number(config.ms) : config.ms;
      const id = setTimeout(() => dispatch(config.msg), msNum);
      return { unsubscribe: () => clearTimeout(id) };
    }

    case 'keyboard': {
      const listener = (e) => {
        const msg = config.handler({
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
      document.addEventListener(config.eventType || 'keydown', listener);
      return {
        unsubscribe: () => document.removeEventListener(config.eventType || 'keydown', listener)
      };
    }

    default:
      console.warn(`Unknown event type: ${type}`);
      return { unsubscribe: () => {} };
  }
}

/**
 * Отписка
 */
export function unsubscribe(subscription) {
  if (subscription && typeof subscription.unsubscribe === 'function') {
    subscription.unsubscribe();
  }
}

/**
 * Утилиты debounce/throttle
 */
export function debounce(fn, ms) {
  let timeoutId;
  return (...args) => {
    clearTimeout(timeoutId);
    timeoutId = setTimeout(() => fn(...args), ms);
  };
}

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
