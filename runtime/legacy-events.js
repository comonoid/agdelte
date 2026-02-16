/**
 * Legacy event subscription for old format {type, config}.
 *
 * Superseded by the modern Event AST interpreted by interpretEvent() in events.js.
 * Kept for backward compatibility with older Agda modules.
 */

/**
 * @param {{ type: string, config: Object }} eventSpec - Legacy event spec
 * @param {Function} dispatch - Message dispatcher
 * @returns {{ unsubscribe: Function }}
 */
export function subscribeLegacy(eventSpec, dispatch) {
  const { type, config } = eventSpec;

  switch (type) {
    case 'never':
      return { unsubscribe: () => {} };

    case 'interval': {
      const msNum = typeof config.ms === 'bigint' ? Number(config.ms) : config.ms;
      // Use handler(Date.now()) if available, fallback to static msg
      const fn = config.handler || (() => config.msg);
      const id = setInterval(() => dispatch(fn(Date.now())), msNum);
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

    case 'clipboardEvent': {
      const listener = (e) => {
        let data = '';
        if (config.event === 'paste') {
          data = (e.clipboardData || window.clipboardData)?.getData('text') || '';
        }
        const msg = config.handler(data);
        if (msg !== null && msg !== undefined) {
          dispatch(msg);
        }
      };
      document.addEventListener(config.event, listener);
      return {
        unsubscribe: () => document.removeEventListener(config.event, listener)
      };
    }

    case 'mouse': {
      const listener = (e) => {
        const msg = config.handler({ x: e.clientX, y: e.clientY, button: e.button });
        if (msg !== null && msg !== undefined) dispatch(msg);
      };
      document.addEventListener(config.eventType, listener);
      return { unsubscribe: () => document.removeEventListener(config.eventType, listener) };
    }

    case 'resize': {
      const listener = () => {
        const msg = config.handler({ width: window.innerWidth, height: window.innerHeight });
        if (msg !== null && msg !== undefined) dispatch(msg);
      };
      window.addEventListener('resize', listener);
      return { unsubscribe: () => window.removeEventListener('resize', listener) };
    }

    case 'scroll': {
      const listener = () => {
        const msg = config.handler({ x: window.scrollX, y: window.scrollY });
        if (msg !== null && msg !== undefined) dispatch(msg);
      };
      window.addEventListener('scroll', listener);
      return { unsubscribe: () => window.removeEventListener('scroll', listener) };
    }

    case 'visibility': {
      const listener = () => {
        const msg = config.handler(document.visibilityState);
        if (msg !== null && msg !== undefined) dispatch(msg);
      };
      document.addEventListener('visibilitychange', listener);
      return { unsubscribe: () => document.removeEventListener('visibilitychange', listener) };
    }

    case 'online': {
      const onlineListener = () => dispatch(config.onOnline);
      const offlineListener = () => dispatch(config.onOffline);
      window.addEventListener('online', onlineListener);
      window.addEventListener('offline', offlineListener);
      return {
        unsubscribe: () => {
          window.removeEventListener('online', onlineListener);
          window.removeEventListener('offline', offlineListener);
        }
      };
    }

    case 'storage': {
      const listener = (e) => {
        if (config.key && e.key !== config.key) return;
        const msg = config.handler(e.newValue);
        if (msg !== null && msg !== undefined) dispatch(msg);
      };
      window.addEventListener('storage', listener);
      return { unsubscribe: () => window.removeEventListener('storage', listener) };
    }

    case 'request': {
      const ctrl = new AbortController();
      (async () => {
        try {
          const { method = 'GET', url, headers = {}, body, onSuccess, onError } = config;
          const response = await fetch(url, { method, headers, body, signal: ctrl.signal });
          if (!response.ok) throw new Error(`HTTP ${response.status}: ${response.statusText}`);
          const data = await response.json();
          dispatch(onSuccess(data));
        } catch (e) {
          if (e.name !== 'AbortError') dispatch(config.onError(e.message));
        }
      })();
      return { unsubscribe: () => ctrl.abort() };
    }

    case 'animationFrame': {
      let running = true;
      const handler = config.msg;
      if (typeof handler === 'function') {
        const loop = (timestamp) => {
          if (!running) return;
          dispatch(handler(String(timestamp)));
          requestAnimationFrame(loop);
        };
        requestAnimationFrame(loop);
      } else {
        const loop = () => {
          if (!running) return;
          dispatch(handler);
          requestAnimationFrame(loop);
        };
        requestAnimationFrame(loop);
      }
      return { unsubscribe: () => { running = false; } };
    }

    default:
      console.warn(`Unknown event type: ${type}`);
      return { unsubscribe: () => {} };
  }
}
