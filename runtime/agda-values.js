/**
 * Agda Value Utilities
 *
 * Scott-encoded format: (cases) => cases.ctor(arg1, arg2, ...)
 *
 * Probing, pattern matching, construction, deep equality,
 * slot-based dependency tracking for reactive bindings.
 */

// ─────────────────────────────────────────────────────────────────────
// Format Detection
// ─────────────────────────────────────────────────────────────────────

/**
 * Check if value is Scott-encoded
 * Format: (cases) => cases.ctor(arg1, arg2, ...)
 */
export function isScottEncoded(value) {
  return typeof value === 'function';
}

/**
 * Check if value is an Agda ADT
 */
export function isAgdaValue(value) {
  return isScottEncoded(value);
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

  // Scott-encoded function
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

  // Scott-encoded object (single-key)
  if (typeof value === 'object') {
    const keys = Object.keys(value);
    if (keys.length === 1 && typeof value[keys[0]] === 'function') {
      const ctor = keys[0];
      let slots = null;
      try {
        slots = value[ctor](new Proxy({}, {
          get(_, name) { return (...args) => args; }
        }));
      } catch { return null; }
      return { ctor, slots: slots || [] };
    }
  }

  return null;
}

// ─────────────────────────────────────────────────────────────────────
// Pattern Matching
// ─────────────────────────────────────────────────────────────────────

/**
 * Match Agda value against cases object (like Scott-encoded call)
 *
 * @param {*} value - Agda value (Scott-encoded)
 * @param {Object} cases - Object with constructor handlers
 * @returns {*} - Result of matched handler
 *
 * @example
 * match(maybeValue, {
 *   just: (x) => x * 2,
 *   nothing: () => 0
 * })
 */
export function match(value, cases) {
  if (!value) {
    throw new Error('match: value is null/undefined');
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
 * Create a Scott-encoded Agda value.
 *
 * @param {string} ctor - Constructor name
 * @param {...*} args - Constructor arguments
 * @returns {Function} - Scott-encoded value
 */
export function construct(ctor, ...args) {
  return (cases) => cases[ctor](...args);
}

// ─────────────────────────────────────────────────────────────────────
// Deep Structural Equality
// ─────────────────────────────────────────────────────────────────────

/**
 * Maximum nesting depth for deep equality comparison.
 * Models with deeper nesting will be assumed equal at the limit,
 * which may skip updates but avoids false re-renders every cycle.
 */
const MAX_DEEP_EQUAL_DEPTH = 50;
let _deepEqualWarnCount = 0;
const _DEEP_EQUAL_WARN_INTERVAL = 100;

export function deepEqual(a, b, depth) {
  if (a === b) return true;
  if (depth > MAX_DEEP_EQUAL_DEPTH) {
    _deepEqualWarnCount++;
    if (_deepEqualWarnCount === 1 || _deepEqualWarnCount % _DEEP_EQUAL_WARN_INTERVAL === 0) {
      console.warn(`deepEqual: max depth (${MAX_DEEP_EQUAL_DEPTH}) exceeded ${_deepEqualWarnCount} time(s), assuming different. Consider flattening your model.`);
    }
    return false;
  }
  const ta = typeof a, tb = typeof b;
  if (ta !== tb) return false;
  if (ta !== 'function' && ta !== 'object') return a === b;
  if (a === null || b === null) return a === b;

  // Plain objects (e.g. from FFI) are not compared structurally — only
  // Scott-encoded functions are. An FFI object will compare by reference (===).
  // This is intentional: Scott values define the Agda model structure.

  // Scott-encoded functions — probe via Proxy
  if (ta === 'function') {
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

  return false;
}

// ─────────────────────────────────────────────────────────────────────
// Slot-based Dependency Tracking
// ─────────────────────────────────────────────────────────────────────

/** Count slots (fields) of a Scott-encoded record */
export function countSlots(model) {
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
export function replaceSlot(model, idx) {
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
 *
 * Algorithm: replace each slot with a unique Symbol sentinel, run extract.
 * If extract throws or returns different value, that slot is a dependency.
 *
 * Returns array of dependent slot indices, or null if detection fails.
 *
 * Complexity: O(N) where N = number of slots. Called once per binding at setup.
 * For models with many fields (>20), consider using nested records.
 */
export function detectSlots(extract, model, numSlots) {
  if (numSlots === 0) return null;

  // Get base value once
  let baseValue;
  try { baseValue = extract(model); } catch { return null; }

  const deps = [];
  for (let i = 0; i < numSlots; i++) {
    const sentinel = Symbol();
    const replaced = (cases) => model(new Proxy({}, {
      get(_, ctorName) {
        return (...args) => {
          const modified = args.slice();
          modified[i] = sentinel;
          return cases[ctorName](...modified);
        };
      }
    }));

    let isDep = false;
    try {
      const modifiedValue = extract(replaced);
      isDep = modifiedValue !== baseValue;
    } catch {
      isDep = true; // if it throws, assume dependency
    }

    if (isDep) deps.push(i);
  }

  return deps.length > 0 ? deps : null;
}

/** Probe a Scott-encoded model, return its constructor args */
const _slotProbe = new Proxy({}, {
  get(_, name) { return (...args) => args; }
});

/**
 * Probe slots from Scott-encoded model.
 * Supports two Agda→JS formats:
 * 1. Function: model(cases) => cases["ctor"](a, b)
 * 2. Object: {ctor: (c) => c.ctor(a, b)}
 */
export function probeSlots(model) {
  if (!model) return null;

  // Format 1: function
  if (typeof model === 'function') {
    try {
      const result = model(_slotProbe);
      return Array.isArray(result) ? result : null;
    } catch { return null; }
  }

  // Format 2: object with single method
  if (typeof model === 'object') {
    const keys = Object.keys(model);
    if (keys.length === 1 && typeof model[keys[0]] === 'function') {
      try { return model[keys[0]](_slotProbe); } catch { return null; }
    }
  }

  return null;
}

/**
 * Probe constructor name of a Scott-encoded value.
 */
export function probeCtor(model) {
  return getCtor(model);
}

/**
 * Detect which top-level slots changed between cached args and new model.
 * scope.cachedArgs stores previous probe result; updated in-place.
 * Returns a Set of changed slot indices, or null if not trackable.
 */
export function changedSlotsFromCache(scope, newModel) {
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
// List Operations
// ─────────────────────────────────────────────────────────────────────

const MAX_LIST_ITEMS = 100000;

/**
 * Convert Agda List to JS Array
 *
 * @param {*} list - Agda List (Scott-encoded)
 * @returns {{ items: Array, incomplete: boolean }}
 */
export function listToArray(list) {
  if (!list) return { items: [], incomplete: false };

  // Already a JS array
  if (Array.isArray(list)) {
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
 * @returns {Function} - Scott-encoded Agda List
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
 * Handles: BigInt, Scott-encoded
 */
export function natToNumber(n) {
  // Already a number
  if (typeof n === 'number') return n;
  if (typeof n === 'bigint') return Number(n);

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
    console.warn(`natToNumber: reached MAX_NAT_VALUE (${MAX_NAT_VALUE}), result may be truncated`);
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
// Numeric Coercion (Agda ℕ → JS number, any representation)
// ─────────────────────────────────────────────────────────────────────

/**
 * Convert Agda numeric value to JS number.
 * Handles BigInt literals, plain numbers, and Scott-encoded ℕ.
 */
export function ensureNumber(n) {
  if (typeof n === 'number') return n;
  if (typeof n === 'bigint') return Number(n);
  return natToNumber(n);
}

// ─────────────────────────────────────────────────────────────────────
// String Coercion (worker/message data → JS string)
// ─────────────────────────────────────────────────────────────────────

/**
 * Ensure a value is a string.
 * If already a string, return as-is. Otherwise JSON.stringify.
 * Used at FFI boundary for worker message data.
 */
export function ensureString(data) {
  return typeof data === 'string' ? data : JSON.stringify(data);
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
// Default export
// ─────────────────────────────────────────────────────────────────────

export default {
  // Detection
  isScottEncoded,
  isAgdaValue,
  // Probing
  getCtor,
  getSlots,
  probe,
  probeSlots,
  probeCtor,
  // Pattern matching
  match,
  matchOr,
  // Construction
  construct,
  // Deep equality
  deepEqual,
  // Slot tracking
  countSlots,
  replaceSlot,
  detectSlots,
  changedSlotsFromCache,
  // Lists
  listToArray,
  arrayToList,
  // Naturals
  natToNumber,
  numberToNat,
  ensureNumber,
  // Strings
  ensureString,
  // Maybe
  fromMaybe,
  toMaybe,
  // Bool
  fromBool,
  toBool
};
