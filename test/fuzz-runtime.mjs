/**
 * Fuzz tests for runtime/agda-values.js and runtime/reactive.js
 *
 * Tests: listToArray, deepEqual, ensureNumber, ensureString,
 *        cloneSlot, wrapMutable, reconcile (extracted from reactive.js)
 */

import {
  listToArray, deepEqual, ensureNumber, ensureString,
  construct, probeSlots, probeCtor, getSlots, getCtor,
  natToNumber, numberToNat, arrayToList
} from '../runtime/agda-values.js';

// ─────────────────────────────────────────────────────────────────────
// Extract unexported functions from reactive.js
// We replicate them here since they are not exported.
// ─────────────────────────────────────────────────────────────────────

function wrapMutable(model, _visited) {
  if (model && model._slots) return model;
  if (model === null || model === undefined) return model;
  if (typeof model !== 'function' && typeof model !== 'object') return model;
  if (!_visited) _visited = new WeakMap();
  if (_visited.has(model)) return _visited.get(model);
  const args = probeSlots(model);
  const ctor = probeCtor(model);
  if (!args || !ctor) return model;
  const slots = [];
  let wrapper;
  if (typeof model === 'function') {
    wrapper = (cases) => cases[ctor](...slots);
  } else {
    wrapper = { [ctor]: (c) => c[ctor](...slots) };
  }
  wrapper._slots = slots;
  wrapper._ctor = ctor;
  _visited.set(model, wrapper);
  for (const a of args) {
    slots.push(
      (typeof a === 'function' || (typeof a === 'object' && a !== null))
        ? wrapMutable(a, _visited)
        : a
    );
  }
  return wrapper;
}

function cloneSlot(s) {
  if (s && s._slots && s._ctor) {
    const clonedSlots = s._slots.map(c => {
      if (c && c._slots && c._ctor) return cloneSlot(c);
      if (typeof c === 'object' && c !== null) {
        try { return structuredClone(c); } catch { return c; }
      }
      return c;
    });
    const ctor = s._ctor;
    if (typeof s === 'function') {
      const w = (cases) => cases[ctor](...clonedSlots);
      w._slots = clonedSlots;
      w._ctor = ctor;
      return w;
    } else {
      const w = { [ctor]: (c) => c[ctor](...clonedSlots) };
      w._slots = clonedSlots;
      w._ctor = ctor;
      return w;
    }
  }
  if (!s) return s;
  if (typeof s === 'object' && s !== null) {
    try { return structuredClone(s); } catch { return s; }
  }
  return s;
}

function reconcile(oldModel, newModel) {
  if (!oldModel || !oldModel._slots) {
    return wrapMutable(newModel);
  }
  const newSlots = getSlots(newModel);
  if (!newSlots) return wrapMutable(newModel);
  const newCtor = getCtor(newModel);
  if (!newCtor || oldModel._ctor !== newCtor) {
    return wrapMutable(newModel);
  }
  const oldSlots = oldModel._slots;
  if (oldSlots.length !== newSlots.length) {
    return wrapMutable(newModel);
  }
  for (let i = 0; i < oldSlots.length; i++) {
    if (oldSlots[i] !== newSlots[i]) {
      const v = newSlots[i];
      oldSlots[i] = (typeof v === 'function' || (typeof v === 'object' && v !== null))
        ? wrapMutable(v)
        : v;
    }
  }
  return oldModel;
}

// ─────────────────────────────────────────────────────────────────────
// Test infrastructure
// ─────────────────────────────────────────────────────────────────────

let passed = 0;
let failed = 0;
const failures = [];

function test(name, fn) {
  try {
    fn();
    passed++;
  } catch (e) {
    failed++;
    failures.push({ name, error: e });
    console.error(`FAIL: ${name}`);
    console.error(`  ${e.message || e}`);
  }
}

function assert(condition, msg) {
  if (!condition) throw new Error(msg || 'assertion failed');
}

// Suppress console.warn/error noise from the functions under test
const origWarn = console.warn;
const origError = console.error;
function hush() {
  console.warn = () => {};
  console.error = () => {};
}
function unhush() {
  console.warn = origWarn;
  console.error = origError;
}

// ─────────────────────────────────────────────────────────────────────
// Helpers
// ─────────────────────────────────────────────────────────────────────

/** Build a Scott-encoded Agda list from array */
function mkList(arr) { return arrayToList(arr); }

/** Build a deeply nested Scott-encoded list of given depth */
function mkDeepList(depth) {
  let list = construct('[]');
  for (let i = 0; i < depth; i++) {
    list = construct('_∷_', i, list);
  }
  return list;
}

/** Build a Scott-encoded Nat of given depth */
function mkNat(n) { return numberToNat(n); }

// =====================================================================
// 1. FUZZ listToArray
// =====================================================================

test('listToArray: null input', () => {
  const r = listToArray(null);
  assert(r.items.length === 0 && !r.incomplete);
});

test('listToArray: undefined input', () => {
  const r = listToArray(undefined);
  assert(r.items.length === 0 && !r.incomplete);
});

test('listToArray: plain JS array passthrough', () => {
  const arr = [1, 2, 3];
  const r = listToArray(arr);
  assert(r.items === arr);
});

test('listToArray: random function (not a list)', () => {
  hush();
  try {
    const r = listToArray(() => 42);
    // Should not crash; may return incomplete
    assert(r !== undefined);
  } finally { unhush(); }
});

test('listToArray: function that throws', () => {
  hush();
  try {
    const r = listToArray(() => { throw new Error('boom'); });
    assert(r !== undefined);
  } finally { unhush(); }
});

test('listToArray: nested list depth 1000', () => {
  hush();
  try {
    const list = mkDeepList(1000);
    const r = listToArray(list);
    assert(r.items.length === 1000, `expected 1000, got ${r.items.length}`);
    assert(!r.incomplete);
  } finally { unhush(); }
});

test('listToArray: list containing BigInt', () => {
  const list = mkList([BigInt(123), BigInt(9007199254740993n)]);
  const r = listToArray(list);
  assert(r.items.length === 2);
  assert(r.items[0] === 123n);
});

test('listToArray: list containing undefined', () => {
  const list = mkList([undefined, undefined]);
  const r = listToArray(list);
  assert(r.items.length === 2);
});

test('listToArray: list containing Symbol', () => {
  const sym = Symbol('test');
  const list = mkList([sym]);
  const r = listToArray(list);
  assert(r.items.length === 1);
  assert(r.items[0] === sym);
});

test('listToArray: circular-ish structure (function referencing itself)', () => {
  hush();
  try {
    // A function that always conses itself — should hit MAX_LIST_ITEMS
    const evil = (cases) => cases['_∷_'](evil, evil);
    const r = listToArray(evil);
    assert(r.incomplete, 'should be incomplete for infinite list');
  } finally { unhush(); }
});

test('listToArray: number input (not a list)', () => {
  hush();
  try {
    const r = listToArray(42);
    assert(r !== undefined);
  } finally { unhush(); }
});

test('listToArray: object input (not a list)', () => {
  hush();
  try {
    const r = listToArray({ foo: 'bar' });
    assert(r !== undefined);
  } finally { unhush(); }
});

test('listToArray: string input', () => {
  hush();
  try {
    const r = listToArray('hello');
    assert(r !== undefined);
  } finally { unhush(); }
});

// =====================================================================
// 2. FUZZ deepEqual
// =====================================================================

test('deepEqual: identical primitives', () => {
  assert(deepEqual(1, 1, 0));
  assert(!deepEqual(1, 2, 0));
  assert(deepEqual('a', 'a', 0));
});

test('deepEqual: NaN slots', () => {
  const a = construct('rec', NaN);
  const b = construct('rec', NaN);
  // NaN !== NaN, so Scott probing will get NaN args; deepEqual recurses
  // but at primitive level NaN !== NaN
  const result = deepEqual(a, b, 0);
  // NaN args should compare as not equal since NaN !== NaN
  assert(!result, 'NaN slots should not be equal');
});

test('deepEqual: Symbol slots', () => {
  const s1 = Symbol('x');
  const s2 = Symbol('x');
  const a = construct('rec', s1);
  const b = construct('rec', s2);
  assert(!deepEqual(a, b, 0), 'different symbols should not be equal');
});

test('deepEqual: same Symbol slot', () => {
  const s = Symbol('x');
  const a = construct('rec', s);
  const b = construct('rec', s);
  assert(deepEqual(a, b, 0), 'same symbol should be equal');
});

test('deepEqual: BigInt slots', () => {
  const a = construct('rec', BigInt(42));
  const b = construct('rec', BigInt(42));
  // BigInt(42) !== BigInt(42) by reference, but 42n === 42n by value
  const result = deepEqual(a, b, 0);
  assert(result, 'equal bigints should be equal');
});

test('deepEqual: shared sub-objects', () => {
  const shared = construct('inner', 1, 2);
  const a = construct('outer', shared, shared);
  const b = construct('outer', shared, shared);
  assert(deepEqual(a, b, 0));
});

test('deepEqual: functions that throw during probing', () => {
  const thrower = () => { throw new Error('probe bomb'); };
  const a = construct('rec', thrower);
  const b = construct('rec', thrower);
  // The thrower is in a slot; deepEqual will try to recurse on it
  // thrower is a function, so deepEqual will try to probe it with Proxy
  // and it will throw, returning false
  const result = deepEqual(a, b, 0);
  // The slot values are the same reference, so the recursive call should
  // short-circuit on a === b
  assert(result, 'same reference throwers should be equal');
});

test('deepEqual: different throwing functions', () => {
  const a = construct('rec', () => { throw new Error('a'); });
  const b = construct('rec', () => { throw new Error('b'); });
  const result = deepEqual(a, b, 0);
  assert(!result, 'different throwing functions should not be equal');
});

test('deepEqual: deeply nested (exceeds MAX_DEEP_EQUAL_DEPTH)', () => {
  hush();
  try {
    // Build nested structure depth > 50
    let a = construct('leaf');
    let b = construct('leaf');
    for (let i = 0; i < 60; i++) {
      a = construct('node', a);
      b = construct('node', b);
    }
    const result = deepEqual(a, b, 0);
    // At depth 50, returns true (assumes equal to avoid infinite re-render)
    assert(result, 'should return true at max depth (assumes equal)');
  } finally { unhush(); }
});

test('deepEqual: null vs function', () => {
  assert(!deepEqual(null, construct('x'), 0));
});

test('deepEqual: both null', () => {
  assert(deepEqual(null, null, 0));
});

test('deepEqual: undefined vs undefined', () => {
  assert(deepEqual(undefined, undefined, 0));
});

test('deepEqual: mismatched constructors', () => {
  const a = construct('left', 1);
  const b = construct('right', 1);
  assert(!deepEqual(a, b, 0));
});

test('deepEqual: mismatched arity', () => {
  const a = construct('rec', 1, 2);
  const b = construct('rec', 1);
  assert(!deepEqual(a, b, 0));
});

// =====================================================================
// 3. FUZZ ensureNumber
// =====================================================================

test('ensureNumber: null', () => {
  const r = ensureNumber(null);
  assert(r === 0, `expected 0, got ${r}`);
});

test('ensureNumber: undefined', () => {
  const r = ensureNumber(undefined);
  assert(r === 0, `expected 0, got ${r}`);
});

test('ensureNumber: NaN', () => {
  const r = ensureNumber(NaN);
  assert(Number.isNaN(r), 'NaN should pass through');
});

test('ensureNumber: Infinity', () => {
  assert(ensureNumber(Infinity) === Infinity);
});

test('ensureNumber: -Infinity', () => {
  assert(ensureNumber(-Infinity) === -Infinity);
});

test('ensureNumber: empty string', () => {
  hush();
  try {
    const r = ensureNumber('');
    assert(r === 0, `expected 0 for empty string, got ${r}`);
  } finally { unhush(); }
});

test('ensureNumber: non-numeric string "abc"', () => {
  hush();
  try {
    const r = ensureNumber('abc');
    assert(typeof r === 'number', `expected number, got ${typeof r}`);
  } finally { unhush(); }
});

test('ensureNumber: BigInt(9007199254740993n)', () => {
  const r = ensureNumber(BigInt(9007199254740993n));
  assert(typeof r === 'number');
  // Note: precision loss is expected
});

test('ensureNumber: Scott Nat depth 100', () => {
  const nat = mkNat(100);
  const r = ensureNumber(nat);
  assert(r === 100, `expected 100, got ${r}`);
});

test('ensureNumber: Scott Nat depth 100000', () => {
  hush();
  try {
    const nat = mkNat(100000);
    const r = ensureNumber(nat);
    assert(r === 100000, `expected 100000, got ${r}`);
  } finally { unhush(); }
});

test('ensureNumber: plain object', () => {
  hush();
  try {
    const r = ensureNumber({ x: 1 });
    assert(typeof r === 'number');
  } finally { unhush(); }
});

test('ensureNumber: array', () => {
  hush();
  try {
    const r = ensureNumber([1, 2, 3]);
    assert(typeof r === 'number');
  } finally { unhush(); }
});

test('ensureNumber: boolean true', () => {
  hush();
  try {
    const r = ensureNumber(true);
    assert(typeof r === 'number');
  } finally { unhush(); }
});

test('ensureNumber: boolean false', () => {
  hush();
  try {
    const r = ensureNumber(false);
    assert(typeof r === 'number');
  } finally { unhush(); }
});

test('ensureNumber: Symbol', () => {
  hush();
  try {
    // Symbol can't be converted to number; natToNumber should handle
    const r = ensureNumber(Symbol('test'));
    assert(typeof r === 'number');
  } finally { unhush(); }
});

// =====================================================================
// 4. FUZZ ensureString
// =====================================================================

test('ensureString: null', () => {
  const r = ensureString(null);
  assert(r === 'null', `expected "null", got ${JSON.stringify(r)}`);
});

test('ensureString: undefined (BUG: returns undefined, not string)', () => {
  const r = ensureString(undefined);
  // JSON.stringify(undefined) returns undefined (not a string)
  assert(typeof r === 'string', `expected string, got ${typeof r}: ${r}`);
});

test('ensureString: Symbol (CRASH: throws TypeError)', () => {
  // JSON.stringify(Symbol()) throws TypeError -- ensureString should handle this
  const r = ensureString(Symbol('test'));
  assert(typeof r === 'string', `expected string, got ${typeof r}`);
});

test('ensureString: BigInt', () => {
  const r = ensureString(BigInt(42));
  assert(r === '42', `expected "42", got ${JSON.stringify(r)}`);
});

test('ensureString: BigInt large', () => {
  const r = ensureString(BigInt(9007199254740993n));
  assert(r === '9007199254740993');
});

test('ensureString: NaN', () => {
  const r = ensureString(NaN);
  assert(r === 'null', `NaN JSON.stringifies to "null", got ${JSON.stringify(r)}`);
});

test('ensureString: Infinity', () => {
  const r = ensureString(Infinity);
  assert(r === 'null', `Infinity JSON.stringifies to "null", got ${JSON.stringify(r)}`);
});

test('ensureString: circular object (CRASH: throws TypeError)', () => {
  const obj = {};
  obj.self = obj;
  // JSON.stringify on circular throws TypeError -- ensureString doesn't catch it
  const r = ensureString(obj);
  assert(typeof r === 'string', `expected string, got ${typeof r}`);
});

test('ensureString: object with toJSON that throws (CRASH: propagates)', () => {
  const obj = { toJSON() { throw new Error('toJSON bomb'); } };
  // JSON.stringify calls toJSON which throws -- ensureString doesn't catch it
  const r = ensureString(obj);
  assert(typeof r === 'string', `expected string, got ${typeof r}`);
});

test('ensureString: number', () => {
  const r = ensureString(42);
  assert(r === '42', `expected "42", got ${JSON.stringify(r)}`);
});

test('ensureString: boolean', () => {
  assert(ensureString(true) === 'true');
  assert(ensureString(false) === 'false');
});

test('ensureString: string passthrough', () => {
  assert(ensureString('hello') === 'hello');
});

test('ensureString: empty string', () => {
  assert(ensureString('') === '');
});

test('ensureString: function (BUG: returns undefined, not string)', () => {
  // JSON.stringify(function) returns undefined
  const r = ensureString(() => 42);
  assert(typeof r === 'string', `expected string, got ${typeof r}: ${r}`);
});

// =====================================================================
// 5. FUZZ cloneSlot / wrapMutable / reconcile
// =====================================================================

test('wrapMutable: null', () => {
  assert(wrapMutable(null) === null);
});

test('wrapMutable: undefined', () => {
  assert(wrapMutable(undefined) === undefined);
});

test('wrapMutable: primitive number', () => {
  assert(wrapMutable(42) === 42);
});

test('wrapMutable: primitive string', () => {
  assert(wrapMutable('hello') === 'hello');
});

test('wrapMutable: Scott-encoded value', () => {
  const val = construct('pair', 1, 'two');
  const wrapped = wrapMutable(val);
  assert(wrapped._slots, 'should have _slots');
  assert(wrapped._ctor === 'pair');
  assert(wrapped._slots[0] === 1);
  assert(wrapped._slots[1] === 'two');
});

test('wrapMutable: nested Scott-encoded', () => {
  const inner = construct('inner', 42);
  const outer = construct('outer', inner, 'x');
  const wrapped = wrapMutable(outer);
  assert(wrapped._slots[0]._slots, 'nested should be wrapped');
  assert(wrapped._slots[0]._slots[0] === 42);
});

test('wrapMutable: already mutable (idempotent)', () => {
  const val = construct('x', 1);
  const w1 = wrapMutable(val);
  const w2 = wrapMutable(w1);
  assert(w1 === w2, 'should return same reference');
});

test('wrapMutable: plain object (not Scott)', () => {
  const obj = { a: 1, b: 2 };
  const result = wrapMutable(obj);
  assert(result === obj, 'non-Scott object should pass through');
});

test('wrapMutable: function that throws', () => {
  const thrower = () => { throw new Error('nope'); };
  const result = wrapMutable(thrower);
  assert(result === thrower, 'throwing function should pass through');
});

test('cloneSlot: null', () => {
  assert(cloneSlot(null) === null);
});

test('cloneSlot: undefined', () => {
  assert(cloneSlot(undefined) === undefined);
});

test('cloneSlot: primitive', () => {
  assert(cloneSlot(42) === 42);
  assert(cloneSlot('hello') === 'hello');
});

test('cloneSlot: mutable wrapper', () => {
  const val = construct('rec', 1, 2);
  const wrapped = wrapMutable(val);
  const cloned = cloneSlot(wrapped);
  assert(cloned !== wrapped, 'should be different reference');
  assert(cloned._slots[0] === 1);
  assert(cloned._slots[1] === 2);
  // Mutation of clone should not affect original
  cloned._slots[0] = 99;
  assert(wrapped._slots[0] === 1, 'original should be unchanged');
});

test('cloneSlot: plain object (structuredClone)', () => {
  const obj = { a: 1, b: [2, 3] };
  const cloned = cloneSlot(obj);
  assert(cloned !== obj);
  assert(cloned.a === 1);
  cloned.b[0] = 99;
  assert(obj.b[0] === 2, 'original should be unchanged');
});

test('cloneSlot: object that fails structuredClone (has function)', () => {
  const obj = { fn: () => 42, x: 1 };
  // structuredClone can't handle functions; should fallback to returning obj
  const cloned = cloneSlot(obj);
  assert(cloned === obj, 'should fallback to same reference');
});

test('reconcile: null oldModel', () => {
  const newModel = construct('rec', 1, 2);
  const result = reconcile(null, newModel);
  assert(result._slots, 'should wrap new model');
});

test('reconcile: non-mutable oldModel', () => {
  const oldModel = construct('rec', 1, 2);
  const newModel = construct('rec', 3, 4);
  const result = reconcile(oldModel, newModel);
  assert(result._slots, 'should wrap');
});

test('reconcile: same constructor, update slots', () => {
  const oldModel = wrapMutable(construct('rec', 1, 2));
  const newModel = construct('rec', 3, 2);
  const result = reconcile(oldModel, newModel);
  assert(result === oldModel, 'should return same reference');
  assert(result._slots[0] === 3, 'slot 0 should be updated');
  assert(result._slots[1] === 2, 'slot 1 unchanged');
});

test('reconcile: different constructors', () => {
  const oldModel = wrapMutable(construct('left', 1));
  const newModel = construct('right', 2);
  const result = reconcile(oldModel, newModel);
  assert(result !== oldModel, 'should create new wrapper');
  assert(result._ctor === 'right');
});

test('reconcile: different arity', () => {
  const oldModel = wrapMutable(construct('rec', 1, 2));
  const newModel = construct('rec', 1, 2, 3);
  const result = reconcile(oldModel, newModel);
  assert(result !== oldModel, 'should create new wrapper for different arity');
});

test('reconcile: newModel is not Scott', () => {
  const oldModel = wrapMutable(construct('rec', 1));
  const result = reconcile(oldModel, 42);
  assert(result === 42, 'non-Scott newModel wraps to itself');
});

test('reconcile: nested model reconciliation', () => {
  const oldModel = wrapMutable(construct('outer', construct('inner', 1), 'x'));
  const newModel = construct('outer', construct('inner', 2), 'x');
  const result = reconcile(oldModel, newModel);
  assert(result === oldModel);
  // The inner slot should be a new wrapped value
  assert(result._slots[0]._slots[0] === 2);
});

// =====================================================================
// Additional edge case fuzzing
// =====================================================================

test('listToArray: very large pre-existing JS array', () => {
  const arr = new Array(100000).fill(0);
  const r = listToArray(arr);
  assert(r.items.length === 100000);
});

test('deepEqual: two identical reference', () => {
  const x = construct('big', 1, 2, 3, 4, 5);
  assert(deepEqual(x, x, 0), 'same reference should be equal');
});

test('deepEqual: function vs non-function', () => {
  assert(!deepEqual(construct('x'), 42, 0));
  assert(!deepEqual(42, construct('x'), 0));
});

test('ensureNumber: zero', () => {
  assert(ensureNumber(0) === 0);
});

test('ensureNumber: negative number', () => {
  assert(ensureNumber(-42) === -42);
});

test('ensureNumber: float', () => {
  assert(ensureNumber(3.14) === 3.14);
});

test('wrapMutable: deeply nested Scott (depth 100)', () => {
  let val = construct('leaf');
  for (let i = 0; i < 100; i++) {
    val = construct('node', val);
  }
  const wrapped = wrapMutable(val);
  // Walk down and verify
  let cur = wrapped;
  let depth = 0;
  while (cur._slots && cur._ctor === 'node') {
    depth++;
    cur = cur._slots[0];
  }
  assert(depth === 100, `expected depth 100, got ${depth}`);
});

test('ensureNumber: Scott Nat depth 200000 (stress)', () => {
  hush();
  try {
    // Build iteratively to avoid stack overflow
    // numberToNat builds using construct() which is recursive... let's be careful
    // Actually numberToNat uses a for loop, so it's fine
    // But 200000 calls to construct creates a chain of closures
    const nat = mkNat(200000);
    const r = ensureNumber(nat);
    // MAX_NAT_VALUE is 100000, so it should be capped
    assert(r === 100000, `expected 100000 (capped), got ${r}`);
  } finally { unhush(); }
});

// =====================================================================
// Report
// =====================================================================

console.log('');
console.log('================================');
console.log(`  PASSED: ${passed}`);
console.log(`  FAILED: ${failed}`);
console.log('================================');

if (failures.length > 0) {
  console.log('\nFailure details:');
  for (const f of failures) {
    console.log(`\n  ${f.name}:`);
    console.log(`    ${f.error.stack || f.error.message || f.error}`);
  }
}

process.exit(failed > 0 ? 1 : 0);
