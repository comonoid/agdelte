/**
 * Agda Value Abstraction Layer
 *
 * Provides uniform interface for both encoding formats:
 * - Scott-encoded: (cases) => cases.ctor(arg1, arg2, ...)
 * - Tagged arrays: ["ctor", arg1, arg2, ...]
 *
 * When the compiler switches to tagged arrays, only this module
 * needs updating — all other runtime code uses these abstractions.
 */

// ─────────────────────────────────────────────────────────────────────
// Format Detection
// ─────────────────────────────────────────────────────────────────────

/**
 * Check if value is a tagged array (future compiler format)
 * Format: ["ctor", arg1, arg2, ...]
 */
export function isTaggedArray(value) {
  return Array.isArray(value) && typeof value[0] === 'string';
}

/**
 * Check if value is Scott-encoded
 * Format: (cases) => cases.ctor(arg1, arg2, ...)
 */
export function isScottEncoded(value) {
  return typeof value === 'function';
}

/**
 * Check if value is an Agda ADT (either format)
 */
export function isAgdaValue(value) {
  return isTaggedArray(value) || isScottEncoded(value);
}

// ─────────────────────────────────────────────────────────────────────
// Probing (Read-only access)
// ─────────────────────────────────────────────────────────────────────

/**
 * Get constructor name from Agda value
 * @returns {string|null}
 */
export function getCtor(value) {
  if (!value) return null;

  // Tagged array
  if (isTaggedArray(value)) {
    return value[0];
  }

  // Scott-encoded function
  if (typeof value === 'function') {
    let ctor = null;
    try {
      value(new Proxy({}, {
        get(_, name) { return (...args) => { ctor = name; }; }
      }));
    } catch { return null; }
    return ctor;
  }

  // Scott-encoded object (single-key)
  if (typeof value === 'object') {
    const keys = Object.keys(value);
    if (keys.length === 1 && typeof value[keys[0]] === 'function') {
      return keys[0];
    }
  }

  return null;
}

/**
 * Get constructor arguments (slots) from Agda value
 * @returns {Array|null}
 */
export function getSlots(value) {
  if (!value) return null;

  // Tagged array
  if (isTaggedArray(value)) {
    return value.slice(1);
  }

  // Scott-encoded function
  if (typeof value === 'function') {
    try {
      return value(new Proxy({}, {
        get(_, name) { return (...args) => args; }
      }));
    } catch { return null; }
  }

  // Scott-encoded object (single-key)
  if (typeof value === 'object') {
    const keys = Object.keys(value);
    if (keys.length === 1 && typeof value[keys[0]] === 'function') {
      try {
        return value[keys[0]](new Proxy({}, {
          get(_, name) { return (...args) => args; }
        }));
      } catch { return null; }
    }
  }

  return null;
}

/**
 * Get both constructor and slots in one probe
 * More efficient when you need both
 * @returns {{ ctor: string, slots: Array }|null}
 */
export function probe(value) {
  if (!value) return null;

  // Tagged array
  if (isTaggedArray(value)) {
    return { ctor: value[0], slots: value.slice(1) };
  }

  // Scott-encoded
  if (typeof value === 'function') {
    let ctor = null;
    let slots = null;
    try {
      value(new Proxy({}, {
        get(_, name) {
          return (...args) => { ctor = name; slots = args; };
        }
      }));
    } catch { return null; }
    return ctor ? { ctor, slots: slots || [] } : null;
  }

  return null;
}

// ─────────────────────────────────────────────────────────────────────
// Pattern Matching
// ─────────────────────────────────────────────────────────────────────

/**
 * Match Agda value against cases object (like Scott-encoded call)
 * Works with both tagged arrays and Scott-encoded values.
 *
 * @param {*} value - Agda value (tagged array or Scott-encoded)
 * @param {Object} cases - Object with constructor handlers
 * @returns {*} - Result of matched handler
 *
 * @example
 * // Works with both formats:
 * match(maybeValue, {
 *   just: (x) => x * 2,
 *   nothing: () => 0
 * })
 */
export function match(value, cases) {
  if (!value) {
    throw new Error('match: value is null/undefined');
  }

  // Tagged array: ["ctor", arg1, arg2, ...]
  if (isTaggedArray(value)) {
    const [ctor, ...args] = value;
    const handler = cases[ctor];
    if (!handler) {
      throw new Error(`match: no handler for constructor "${ctor}"`);
    }
    return handler(...args);
  }

  // Scott-encoded: call value with cases
  if (typeof value === 'function') {
    return value(cases);
  }

  // Scott-encoded object format
  if (typeof value === 'object') {
    const keys = Object.keys(value);
    if (keys.length === 1 && typeof value[keys[0]] === 'function') {
      return value[keys[0]](cases);
    }
  }

  throw new Error(`match: unsupported value type: ${typeof value}`);
}

/**
 * Safe match with default for missing constructors
 * @param {*} value
 * @param {Object} cases
 * @param {*} defaultValue
 */
export function matchOr(value, cases, defaultValue) {
  try {
    return match(value, cases);
  } catch {
    return defaultValue;
  }
}

// ─────────────────────────────────────────────────────────────────────
// Construction (Creating Agda values)
// ─────────────────────────────────────────────────────────────────────

/**
 * Create an Agda value in the current encoding format.
 * Set AGDA_USE_TAGGED_ARRAYS=true to use tagged arrays.
 *
 * @param {string} ctor - Constructor name
 * @param {...*} args - Constructor arguments
 * @returns {*} - Agda value (tagged array or Scott-encoded)
 */
export function construct(ctor, ...args) {
  if (typeof globalThis !== 'undefined' && globalThis.AGDA_USE_TAGGED_ARRAYS) {
    // Tagged array format
    return [ctor, ...args];
  }
  // Scott-encoded format (default)
  return (cases) => cases[ctor](...args);
}

/**
 * Create a tagged array (explicit format)
 */
export function tagged(ctor, ...args) {
  return [ctor, ...args];
}

/**
 * Create a Scott-encoded value (explicit format)
 */
export function scott(ctor, ...args) {
  return (cases) => cases[ctor](...args);
}

// ─────────────────────────────────────────────────────────────────────
// List Operations
// ─────────────────────────────────────────────────────────────────────

const MAX_LIST_ITEMS = 100000;

/**
 * Convert Agda List to JS Array
 * Handles both tagged arrays and Scott-encoded lists.
 *
 * @param {*} list - Agda List
 * @returns {{ items: Array, incomplete: boolean }}
 */
export function listToArray(list) {
  if (!list) return { items: [], incomplete: false };

  // Already a JS array (not tagged)
  if (Array.isArray(list) && !isTaggedArray(list)) {
    return { items: list, incomplete: false };
  }

  const result = [];
  let current = list;
  let iterations = 0;

  while (true) {
    if (iterations++ > MAX_LIST_ITEMS) {
      console.error('listToArray: possible infinite loop');
      return { items: result, incomplete: true };
    }

    // Tagged array format
    if (isTaggedArray(current)) {
      const [ctor, ...args] = current;
      if (ctor === '[]') break;
      if (ctor === '_∷_') {
        result.push(args[0]);
        current = args[1];
        continue;
      }
      console.warn(`listToArray: unexpected constructor "${ctor}"`);
      return { items: result, incomplete: true };
    }

    // Scott-encoded format
    if (typeof current === 'function') {
      const done = current({
        '[]': () => true,
        '_∷_': (head, tail) => {
          result.push(head);
          current = tail;
          return false;
        }
      });
      if (done) break;
      continue;
    }

    console.warn('listToArray: unexpected element type', typeof current);
    return { items: result, incomplete: true };
  }

  return { items: result, incomplete: false };
}

/**
 * Convert JS Array to Agda List
 * @param {Array} arr
 * @returns {*} - Agda List (in current encoding format)
 */
export function arrayToList(arr) {
  let result = construct('[]');
  for (let i = arr.length - 1; i >= 0; i--) {
    result = construct('_∷_', arr[i], result);
  }
  return result;
}

// ─────────────────────────────────────────────────────────────────────
// Natural Numbers
// ─────────────────────────────────────────────────────────────────────

const MAX_NAT_VALUE = 100000;

/**
 * Convert Agda ℕ to JS number
 * Handles: BigInt, tagged array (zero/suc), Scott-encoded
 */
export function natToNumber(n) {
  // Already a number
  if (typeof n === 'number') return n;
  if (typeof n === 'bigint') return Number(n);

  // Tagged array
  if (isTaggedArray(n)) {
    let count = 0;
    let current = n;
    while (count < MAX_NAT_VALUE) {
      if (current[0] === 'zero') return count;
      if (current[0] === 'suc') {
        count++;
        current = current[1];
        continue;
      }
      break;
    }
    console.warn('natToNumber: exceeded max or invalid structure');
    return count;
  }

  // Scott-encoded
  if (typeof n === 'function') {
    let count = 0;
    let current = n;
    while (count < MAX_NAT_VALUE) {
      let result = null;
      try {
        current({
          zero: () => { result = 'zero'; },
          suc: (pred) => { result = pred; }
        });
      } catch { break; }
      if (result === 'zero') return count;
      if (result !== null) {
        count++;
        current = result;
        continue;
      }
      break;
    }
    return count;
  }

  return 0;
}

/**
 * Convert JS number to Agda ℕ
 */
export function numberToNat(num) {
  let result = construct('zero');
  for (let i = 0; i < num; i++) {
    result = construct('suc', result);
  }
  return result;
}

// ─────────────────────────────────────────────────────────────────────
// Maybe Operations
// ─────────────────────────────────────────────────────────────────────

/**
 * Extract value from Agda Maybe
 * @returns {*} - The value or null if nothing
 */
export function fromMaybe(maybe) {
  if (!maybe) return null;

  return matchOr(maybe, {
    just: (x) => x,
    nothing: () => null
  }, null);
}

/**
 * Create Agda Maybe from nullable value
 */
export function toMaybe(value) {
  return value != null
    ? construct('just', value)
    : construct('nothing');
}

// ─────────────────────────────────────────────────────────────────────
// Boolean Operations
// ─────────────────────────────────────────────────────────────────────

/**
 * Convert Agda Bool to JS boolean
 */
export function fromBool(bool) {
  if (typeof bool === 'boolean') return bool;

  return matchOr(bool, {
    true: () => true,
    false: () => false
  }, false);
}

/**
 * Convert JS boolean to Agda Bool
 */
export function toBool(value) {
  return value ? construct('true') : construct('false');
}

// ─────────────────────────────────────────────────────────────────────
// Deep Equality
// ─────────────────────────────────────────────────────────────────────

const MAX_DEEP_EQUAL_DEPTH = 20;

/**
 * Deep structural equality for Agda values
 * Works with both tagged arrays and Scott-encoded values
 */
export function deepEqual(a, b, depth = 0) {
  if (a === b) return true;
  if (depth > MAX_DEEP_EQUAL_DEPTH) return false;

  const ta = typeof a, tb = typeof b;
  if (ta !== tb) return false;

  // Primitives
  if (ta !== 'function' && ta !== 'object') return a === b;
  if (a === null || b === null) return a === b;

  // Tagged arrays
  if (isTaggedArray(a) && isTaggedArray(b)) {
    if (a.length !== b.length) return false;
    for (let i = 0; i < a.length; i++) {
      if (!deepEqual(a[i], b[i], depth + 1)) return false;
    }
    return true;
  }

  // Scott-encoded
  if (typeof a === 'function' && typeof b === 'function') {
    const probeA = probe(a);
    const probeB = probe(b);
    if (!probeA || !probeB) return false;
    if (probeA.ctor !== probeB.ctor) return false;
    if (probeA.slots.length !== probeB.slots.length) return false;
    for (let i = 0; i < probeA.slots.length; i++) {
      if (!deepEqual(probeA.slots[i], probeB.slots[i], depth + 1)) return false;
    }
    return true;
  }

  return false;
}

// ─────────────────────────────────────────────────────────────────────
// Exports for backward compatibility
// ─────────────────────────────────────────────────────────────────────

export default {
  // Detection
  isTaggedArray,
  isScottEncoded,
  isAgdaValue,
  // Probing
  getCtor,
  getSlots,
  probe,
  // Pattern matching
  match,
  matchOr,
  // Construction
  construct,
  tagged,
  scott,
  // Lists
  listToArray,
  arrayToList,
  // Naturals
  natToNumber,
  numberToNat,
  // Maybe
  fromMaybe,
  toMaybe,
  // Bool
  fromBool,
  toBool,
  // Equality
  deepEqual
};
