/**
 * Scott-encoding utilities for Agda values
 *
 * Deep equality, slot probing, constructor detection,
 * and dependency tracking for reactive bindings.
 */

// ─────────────────────────────────────────────────────────────────────
// Deep structural equality for Scott-encoded Agda values
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
      console.warn(`deepEqual: max depth (${MAX_DEEP_EQUAL_DEPTH}) exceeded ${_deepEqualWarnCount} time(s), assuming equal. Consider flattening your model.`);
    }
    return true;
  }
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
 * Optimization: Most bindings depend on 1 slot. Once we find 2+ dependencies,
 * we return null (skip optimization, fall through to full check).
 *
 * Complexity: O(N) where N = number of slots. Called once per binding at setup.
 * For models with many fields (>20), consider using nested records.
 */
export function detectSlots(extract, model, numSlots) {
  if (numSlots === 0) return null;

  // Get base value once
  let baseValue;
  try { baseValue = extract(model); } catch { return null; }

  // Fast path: probe slots until we find ≤1 dependency
  // If 2+ deps found, return null (too complex for slot optimization)
  let singleDep = -1;  // -1 = none found, ≥0 = slot index
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

    if (isDep) {
      if (singleDep >= 0) {
        // Found 2nd dependency - fall back to full check mode
        return null;
      }
      singleDep = i;
    }
  }

  return singleDep >= 0 ? [singleDep] : null;
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
 * Supports both function and object formats.
 */
export function probeCtor(model) {
  if (!model) return null;

  // Format 1: function
  if (typeof model === 'function') {
    let ctor = null;
    try {
      model(new Proxy({}, {
        get(_, name) { return (...args) => { ctor = name; }; }
      }));
    } catch { return null; }
    return ctor;
  }

  // Format 2: object with single method — key IS the ctor name
  if (typeof model === 'object') {
    const keys = Object.keys(model);
    if (keys.length === 1 && typeof model[keys[0]] === 'function') {
      return keys[0];
    }
  }

  return null;
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
