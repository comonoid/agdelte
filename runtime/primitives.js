/**
 * Agdelte Runtime - FFI Primitives
 * JavaScript implementations for Agda FFI
 */

// ========================================
// Interval
// ========================================

/**
 * Create an interval event
 * @param {number} ms - Interval in milliseconds
 * @param {*} msg - Message to dispatch
 * @returns {Object} - Event spec
 */
export function interval(ms) {
  return (msg) => ({
    type: 'interval',
    config: { ms, msg }
  });
}

/**
 * Create a one-shot timer event
 */
export function timeout(ms) {
  return (msg) => ({
    type: 'timeout',
    config: { ms, msg }
  });
}

// ========================================
// Animation Frame
// ========================================

/**
 * Animation frame event
 */
export function animationFrame(msg) {
  return {
    type: 'animationFrame',
    config: { msg }
  };
}

/**
 * Animation frame event with timestamp
 */
export function animationFrameWithTime(handler) {
  return {
    type: 'animationFrame',
    config: { msg: handler }
  };
}

// ========================================
// Keyboard
// ========================================

/**
 * Subscribe to key presses
 */
export function onKeyDown(handler) {
  return {
    type: 'keyboard',
    config: { eventType: 'keydown', handler }
  };
}

export function onKeyUp(handler) {
  return {
    type: 'keyboard',
    config: { eventType: 'keyup', handler }
  };
}

/**
 * Subscribe to a specific key
 */
export function onKey(key) {
  return (msg) => ({
    type: 'keyboard',
    config: {
      eventType: 'keydown',
      handler: (e) => e.key === key ? msg : null
    }
  });
}

/**
 * Subscribe to arrow keys
 */
export function onArrowKeys(handler) {
  return {
    type: 'keyboard',
    config: {
      eventType: 'keydown',
      handler: (e) => {
        switch (e.key) {
          case 'ArrowUp': return handler.up;
          case 'ArrowDown': return handler.down;
          case 'ArrowLeft': return handler.left;
          case 'ArrowRight': return handler.right;
          default: return null;
        }
      }
    }
  };
}

// ========================================
// Mouse
// ========================================

/**
 * Mouse position
 */
export function onMouseMove(handler) {
  return {
    type: 'mouse',
    config: { eventType: 'mousemove', handler }
  };
}

export function onMouseDown(handler) {
  return {
    type: 'mouse',
    config: { eventType: 'mousedown', handler }
  };
}

export function onMouseUp(handler) {
  return {
    type: 'mouse',
    config: { eventType: 'mouseup', handler }
  };
}

export function onClick(handler) {
  return {
    type: 'mouse',
    config: { eventType: 'click', handler }
  };
}

// ========================================
// Window events
// ========================================

export function onResize(handler) {
  return {
    type: 'resize',
    config: { handler }
  };
}

export function onScroll(handler) {
  return {
    type: 'scroll',
    config: { handler }
  };
}

export function onVisibilityChange(handler) {
  return {
    type: 'visibility',
    config: { handler }
  };
}

export function onOnlineStatus(onOnline, onOffline) {
  return {
    type: 'online',
    config: { onOnline, onOffline }
  };
}

// ========================================
// HTTP Requests
// ========================================

/**
 * Create an HTTP request
 */
export function httpRequest(config) {
  return (onSuccess) => (onError) => ({
    type: 'request',
    config: { ...config, onSuccess, onError }
  });
}

/**
 * GET request
 */
export function httpGet(url) {
  return httpRequest({ method: 'GET', url });
}

/**
 * POST request
 */
export function httpPost(url, body) {
  return httpRequest({
    method: 'POST',
    url,
    body: JSON.stringify(body),
    headers: { 'Content-Type': 'application/json' }
  });
}

/**
 * Perform an HTTP request and invoke callback
 */
export async function performRequest(config, dispatch) {
  const { method = 'GET', url, headers = {}, body, onSuccess, onError } = config;

  try {
    const response = await fetch(url, {
      method,
      headers,
      body
    });

    if (!response.ok) {
      throw new Error(`HTTP ${response.status}: ${response.statusText}`);
    }

    const data = await response.json();
    dispatch(onSuccess(data));
  } catch (error) {
    dispatch(onError(error.message));
  }
}

// ========================================
// Time
// ========================================

/**
 * Current time in milliseconds
 */
export function now() {
  return Date.now();
}

/**
 * Current time as Date
 */
export function currentTime() {
  return new Date();
}

/**
 * Periodic time
 */
export function every(ms) {
  return (handler) => ({
    type: 'interval',
    config: {
      ms,
      handler
    }
  });
}

// ========================================
// Random
// ========================================

/**
 * Random number
 */
export function random() {
  return Math.random();
}

/**
 * Random integer in range [min, max]
 */
export function randomInt(min, max) {
  return Math.floor(Math.random() * (max - min + 1)) + min;
}

/**
 * Random element from array
 */
export function randomElement(arr) {
  return arr[randomInt(0, arr.length - 1)];
}

// ========================================
// Local Storage
// ========================================

export function getItem(key) {
  try {
    const value = localStorage.getItem(key);
    return value !== null ? JSON.parse(value) : null;
  } catch {
    return null;
  }
}

export function setItem(key, value) {
  try {
    localStorage.setItem(key, JSON.stringify(value));
    return true;
  } catch {
    return false;
  }
}

export function removeItem(key) {
  localStorage.removeItem(key);
}

export function onStorageChange(key, handler) {
  return {
    type: 'storage',
    config: { key, handler }
  };
}

// ========================================
// Console (debugging)
// ========================================

export function log(msg) {
  console.log('[Agdelte]', msg);
  return msg;
}

export function trace(label) {
  return (value) => {
    console.log(`[Agdelte:${label}]`, value);
    return value;
  };
}

// ========================================
// Debounce / Throttle for Events
// ========================================

export function debounced(ms) {
  return (eventSpec) => ({
    ...eventSpec,
    debounce: ms
  });
}

export function throttled(ms) {
  return (eventSpec) => ({
    ...eventSpec,
    throttle: ms
  });
}

// ========================================
// Agda FFI exports
// ========================================

// These functions correspond to COMPILE JS pragmas in Agda

export const AgdeltePrimitives = {
  // Interval
  interval,
  timeout,

  // Animation
  animationFrame,
  animationFrameWithTime,

  // Keyboard
  onKeyDown,
  onKeyUp,
  onKey,
  onArrowKeys,

  // Mouse
  onMouseMove,
  onMouseDown,
  onMouseUp,
  onClick,

  // Window
  onResize,
  onScroll,
  onVisibilityChange,
  onOnlineStatus,

  // HTTP
  httpGet,
  httpPost,
  httpRequest,
  performRequest,

  // Time
  now,
  currentTime,
  every,

  // Random
  random,
  randomInt,
  randomElement,

  // Storage
  getItem,
  setItem,
  removeItem,
  onStorageChange,

  // Debug
  log,
  trace,

  // Modifiers
  debounced,
  throttled
};

// For browser usage
if (typeof window !== 'undefined') {
  window.AgdeltePrimitives = AgdeltePrimitives;
}

export default AgdeltePrimitives;
