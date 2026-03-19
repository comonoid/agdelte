/**
 * Fuzz tests for runtime/agda-values.js and runtime/reactive.js
 *
 * Tests: listToArray, deepEqual, ensureNumber, ensureString,
 *        cloneSlot, wrapMutable, reconcile (extracted from reactive.js)
 */

import {
  listToArray, deepEqual, ensureNumber, ensureString,
  construct, probeSlots, probeCtor, getSlots, getCtor,
  natToNumber, numberToNat, arrayToList,
  probe, matchOr, fromMaybe, toMaybe, fromBool, toBool
} from '../runtime/agda-values.js';

import { wrapMutable, cloneSlot, reconcile } from '../runtime/reactive.js';

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

test('deepEqual: NaN slots treated as equal', () => {
  const a = construct('rec', NaN);
  const b = construct('rec', NaN);
  // NaN === NaN is false in JS, but deepEqual treats NaN as equal
  // to prevent infinite re-render loops when model slots contain NaN.
  const result = deepEqual(a, b, 0);
  assert(result, 'NaN slots should be treated as equal to avoid re-render loops');
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

test('ensureString: undefined', () => {
  const r = ensureString(undefined);
  assert(typeof r === 'string', `expected string, got ${typeof r}: ${r}`);
});

test('ensureString: Symbol', () => {
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

test('ensureString: circular object', () => {
  const obj = {};
  obj.self = obj;
  const r = ensureString(obj);
  assert(typeof r === 'string', `expected string, got ${typeof r}`);
});

test('ensureString: object with toJSON that throws', () => {
  const obj = { toJSON() { throw new Error('toJSON bomb'); } };
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

test('ensureString: function', () => {
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
  // structuredClone can't handle functions; should fallback to shallow clone
  const cloned = cloneSlot(obj);
  assert(cloned !== obj, 'should return a shallow clone, not the same reference');
  assert(cloned.x === 1, 'should preserve primitive properties');
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

test('ensureNumber: null returns 0 with warning', () => {
  hush();
  try {
    assert(ensureNumber(null) === 0, 'null should return 0');
  } finally { unhush(); }
});

test('ensureNumber: undefined returns 0 with warning', () => {
  hush();
  try {
    assert(ensureNumber(undefined) === 0, 'undefined should return 0');
  } finally { unhush(); }
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
// 6. FUZZ probe
// =====================================================================

test('probe: null', () => {
  assert(probe(null) === null);
});

test('probe: undefined', () => {
  assert(probe(undefined) === null);
});

test('probe: primitive number', () => {
  assert(probe(42) === null);
});

test('probe: primitive string', () => {
  assert(probe('hello') === null);
});

test('probe: Scott-encoded value', () => {
  const val = construct('pair', 1, 'two');
  const result = probe(val);
  assert(result !== null, 'should probe successfully');
  assert(result.ctor === 'pair', `expected ctor "pair", got "${result.ctor}"`);
  assert(result.slots.length === 2, `expected 2 slots, got ${result.slots.length}`);
  assert(result.slots[0] === 1);
  assert(result.slots[1] === 'two');
});

test('probe: nullary constructor', () => {
  const val = construct('nothing');
  const result = probe(val);
  assert(result !== null);
  assert(result.ctor === 'nothing');
  assert(result.slots.length === 0);
});

test('probe: function that throws', () => {
  const thrower = () => { throw new Error('boom'); };
  const result = probe(thrower);
  assert(result === null, 'throwing function should return null');
});

test('probe: plain object (not Scott)', () => {
  const obj = { a: 1, b: 2 };
  assert(probe(obj) === null, 'multi-key object should return null');
});

test('probe: boolean false', () => {
  assert(probe(false) === null);
});

test('probe: nested Scott value', () => {
  const inner = construct('leaf', 42);
  const outer = construct('node', inner);
  const result = probe(outer);
  assert(result !== null);
  assert(result.ctor === 'node');
  // The slot should be the inner Scott function
  const innerResult = probe(result.slots[0]);
  assert(innerResult !== null);
  assert(innerResult.ctor === 'leaf');
  assert(innerResult.slots[0] === 42);
});

// =====================================================================
// 7. FUZZ matchOr
// =====================================================================

test('matchOr: matching constructor', () => {
  const val = construct('just', 42);
  const result = matchOr(val, { just: (x) => x * 2, nothing: () => 0 }, -1);
  assert(result === 84, `expected 84, got ${result}`);
});

test('matchOr: missing constructor falls back to default', () => {
  const val = construct('just', 42);
  const result = matchOr(val, { nothing: () => 0 }, -1);
  assert(result === -1, `expected -1, got ${result}`);
});

test('matchOr: null value returns default', () => {
  const result = matchOr(null, { just: (x) => x }, 'default');
  assert(result === 'default', `expected "default", got ${result}`);
});

test('matchOr: undefined value returns default', () => {
  const result = matchOr(undefined, { just: (x) => x }, 'default');
  assert(result === 'default');
});

test('matchOr: primitive value returns default', () => {
  const result = matchOr(42, { just: (x) => x }, 'default');
  assert(result === 'default');
});

test('matchOr: handler that throws returns default', () => {
  const val = construct('boom');
  const result = matchOr(val, { boom: () => { throw new Error('kaboom'); } }, 'safe');
  // matchOr catches match errors, but the handler throw may propagate
  // depending on implementation — the key is it doesn't crash
  assert(typeof result !== 'undefined');
});

test('matchOr: Scott value with multiple slots', () => {
  const val = construct('triple', 1, 2, 3);
  const result = matchOr(val, { triple: (a, b, c) => a + b + c }, 0);
  assert(result === 6, `expected 6, got ${result}`);
});

// =====================================================================
// 8. FUZZ fromMaybe
// =====================================================================

test('fromMaybe: just value', () => {
  const val = construct('just', 42);
  const result = fromMaybe(val);
  assert(result === 42, `expected 42, got ${result}`);
});

test('fromMaybe: nothing', () => {
  const val = construct('nothing');
  const result = fromMaybe(val);
  assert(result === null, `expected null, got ${result}`);
});

test('fromMaybe: null input', () => {
  assert(fromMaybe(null) === null);
});

test('fromMaybe: undefined input', () => {
  assert(fromMaybe(undefined) === null);
});

test('fromMaybe: primitive input', () => {
  const result = fromMaybe(42);
  assert(result === null, 'non-Maybe value should return null');
});

test('fromMaybe: just with nested Scott value', () => {
  const inner = construct('pair', 'a', 'b');
  const val = construct('just', inner);
  const result = fromMaybe(val);
  const probed = probe(result);
  assert(probed !== null);
  assert(probed.ctor === 'pair');
});

test('fromMaybe: just null', () => {
  const val = construct('just', null);
  const result = fromMaybe(val);
  assert(result === null, 'just(null) extracts to null');
});

test('fromMaybe: just undefined', () => {
  const val = construct('just', undefined);
  const result = fromMaybe(val);
  assert(result === undefined, 'just(undefined) extracts to undefined');
});

// =====================================================================
// 9. FUZZ toMaybe
// =====================================================================

test('toMaybe: non-null value', () => {
  const result = toMaybe(42);
  const probed = probe(result);
  assert(probed !== null, 'should be Scott-encoded');
  assert(probed.ctor === 'just');
  assert(probed.slots[0] === 42);
});

test('toMaybe: string value', () => {
  const result = toMaybe('hello');
  const probed = probe(result);
  assert(probed.ctor === 'just');
  assert(probed.slots[0] === 'hello');
});

test('toMaybe: null', () => {
  const result = toMaybe(null);
  const probed = probe(result);
  assert(probed !== null);
  assert(probed.ctor === 'nothing');
  assert(probed.slots.length === 0);
});

test('toMaybe: undefined', () => {
  const result = toMaybe(undefined);
  const probed = probe(result);
  assert(probed !== null);
  assert(probed.ctor === 'nothing');
});

test('toMaybe: false (truthy check)', () => {
  // false is non-null/non-undefined, so should be just(false)
  const result = toMaybe(false);
  const probed = probe(result);
  // toMaybe uses != null, so false is non-null → just
  assert(probed.ctor === 'just');
  assert(probed.slots[0] === false);
});

test('toMaybe: zero', () => {
  const result = toMaybe(0);
  const probed = probe(result);
  assert(probed.ctor === 'just');
  assert(probed.slots[0] === 0);
});

test('toMaybe: empty string', () => {
  const result = toMaybe('');
  const probed = probe(result);
  assert(probed.ctor === 'just');
  assert(probed.slots[0] === '');
});

test('toMaybe: roundtrip with fromMaybe', () => {
  assert(fromMaybe(toMaybe(42)) === 42);
  assert(fromMaybe(toMaybe(null)) === null);
  assert(fromMaybe(toMaybe('test')) === 'test');
});

// =====================================================================
// 10. FUZZ fromBool
// =====================================================================

test('fromBool: JS true passthrough', () => {
  assert(fromBool(true) === true);
});

test('fromBool: JS false passthrough', () => {
  assert(fromBool(false) === false);
});

test('fromBool: Scott true', () => {
  const val = construct('true');
  assert(fromBool(val) === true);
});

test('fromBool: Scott false', () => {
  const val = construct('false');
  assert(fromBool(val) === false);
});

test('fromBool: null returns false (default)', () => {
  assert(fromBool(null) === false);
});

test('fromBool: undefined returns false (default)', () => {
  assert(fromBool(undefined) === false);
});

test('fromBool: non-bool Scott value returns false (default)', () => {
  const val = construct('just', 42);
  assert(fromBool(val) === false);
});

test('fromBool: number returns false (default)', () => {
  // Numbers are not booleans and not Scott
  assert(fromBool(1) === false);
});

// =====================================================================
// 11. FUZZ toBool
// =====================================================================

test('toBool: truthy value', () => {
  const result = toBool(true);
  const probed = probe(result);
  assert(probed !== null);
  assert(probed.ctor === 'true');
});

test('toBool: falsy value (false)', () => {
  const result = toBool(false);
  const probed = probe(result);
  assert(probed !== null);
  assert(probed.ctor === 'false');
});

test('toBool: falsy value (0)', () => {
  const result = toBool(0);
  const probed = probe(result);
  assert(probed.ctor === 'false');
});

test('toBool: falsy value (null)', () => {
  const result = toBool(null);
  const probed = probe(result);
  assert(probed.ctor === 'false');
});

test('toBool: falsy value (undefined)', () => {
  const result = toBool(undefined);
  const probed = probe(result);
  assert(probed.ctor === 'false');
});

test('toBool: falsy value (empty string)', () => {
  const result = toBool('');
  const probed = probe(result);
  assert(probed.ctor === 'false');
});

test('toBool: truthy value (non-empty string)', () => {
  const result = toBool('hello');
  const probed = probe(result);
  assert(probed.ctor === 'true');
});

test('toBool: truthy value (number 1)', () => {
  const result = toBool(1);
  const probed = probe(result);
  assert(probed.ctor === 'true');
});

test('toBool: truthy value (object)', () => {
  const result = toBool({});
  const probed = probe(result);
  assert(probed.ctor === 'true');
});

test('toBool: roundtrip with fromBool', () => {
  assert(fromBool(toBool(true)) === true);
  assert(fromBool(toBool(false)) === false);
  assert(fromBool(toBool(1)) === true);
  assert(fromBool(toBool(0)) === false);
  assert(fromBool(toBool(null)) === false);
});

// =====================================================================
// 12. FUZZ ensureString edge cases
// =====================================================================

test('ensureString: circular object', () => {
  const obj = {};
  obj.self = obj;
  const result = ensureString(obj);
  // JSON.stringify will throw on circular, fallback to String(obj)
  assert(typeof result === 'string', 'should return a string for circular object');
});

test('ensureString: Symbol', () => {
  const result = ensureString(Symbol('test'));
  assert(typeof result === 'string');
  assert(result.includes('test'), `symbol string should contain name, got: ${result}`);
});

test('ensureString: BigInt', () => {
  const result = ensureString(42n);
  assert(result === '42', `BigInt should stringify, got: ${result}`);
});

test('ensureString: function', () => {
  const result = ensureString(() => {});
  assert(result === '[function]', `function should return [function], got: ${result}`);
});

test('ensureString: null', () => {
  assert(ensureString(null) === 'null');
});

test('ensureString: undefined', () => {
  assert(ensureString(undefined) === 'undefined');
});

test('ensureString: nested object', () => {
  const result = ensureString({ a: 1, b: [2, 3] });
  assert(result.includes('"a"'), 'should JSON.stringify nested object');
});

test('ensureString: empty string passthrough', () => {
  assert(ensureString('') === '');
});

// =====================================================================
// 13. FUZZ isScottEncoded / isAgdaValue
// =====================================================================

import { isScottEncoded, isAgdaValue, replaceSlot } from '../runtime/agda-values.js';

test('isScottEncoded: Scott function', () => {
  const val = construct('pair', 1, 2);
  assert(isScottEncoded(val) === true, 'Scott function should be detected');
});

test('isScottEncoded: plain function is also true (any function)', () => {
  // isScottEncoded simply checks typeof === 'function'
  assert(isScottEncoded(() => {}) === true, 'any function is considered Scott-encoded');
});

test('isScottEncoded: object-format Scott', () => {
  const val = { pair: (c) => c.pair(1, 2) };
  // isScottEncoded checks for single-key object with function value
  const result = isScottEncoded(val);
  assert(typeof result === 'boolean', 'should return boolean');
});

test('isScottEncoded: primitives', () => {
  assert(isScottEncoded(null) === false);
  assert(isScottEncoded(undefined) === false);
  assert(isScottEncoded(42) === false);
  assert(isScottEncoded('hello') === false);
  assert(isScottEncoded(true) === false);
});

test('isAgdaValue: Scott-encoded', () => {
  const val = construct('just', 42);
  assert(isAgdaValue(val) === true, 'Scott function should be Agda value');
});

test('isAgdaValue: primitives', () => {
  assert(isAgdaValue(null) === false);
  assert(isAgdaValue(42) === false);
});

// =====================================================================
// 14. FUZZ replaceSlot
// =====================================================================

test('replaceSlot: returns a function wrapper', () => {
  // replaceSlot returns a Scott-encoded value that, when called with cases,
  // invokes the original but with slot[idx] replaced by a sentinel Symbol
  const val = construct('pair', 'a', 'b');
  const replaced = replaceSlot(val, 0);
  assert(typeof replaced === 'function', 'replaceSlot should return function');

  // Call with cases to extract slots
  let gotSlots = null;
  replaced({ pair: (...args) => { gotSlots = args; } });
  assert(gotSlots !== null, 'should invoke cases');
  assert(typeof gotSlots[0] === 'symbol', 'slot 0 should be replaced with sentinel Symbol');
  assert(gotSlots[1] === 'b', `slot 1 should be unchanged, got ${gotSlots[1]}`);
});

test('replaceSlot: replace last slot', () => {
  const val = construct('triple', 1, 2, 3);
  const replaced = replaceSlot(val, 2);
  let gotSlots = null;
  replaced({ triple: (...args) => { gotSlots = args; } });
  assert(typeof gotSlots[2] === 'symbol', 'slot 2 should be sentinel');
  assert(gotSlots[0] === 1, 'slot 0 unchanged');
  assert(gotSlots[1] === 2, 'slot 1 unchanged');
});

// =====================================================================
// 15. FUZZ arrayToList / listToArray roundtrip
// =====================================================================

test('arrayToList -> listToArray roundtrip: empty', () => {
  const list = arrayToList([]);
  const result = listToArray(list);
  assert(result.items.length === 0, 'empty roundtrip');
  assert(!result.incomplete, 'should be complete');
});

test('arrayToList -> listToArray roundtrip: 5 elements', () => {
  const original = [1, 2, 3, 4, 5];
  const list = arrayToList(original);
  const result = listToArray(list);
  for (let i = 0; i < 5; i++) {
    assert(result.items[i] === original[i], `element ${i} should match`);
  }
});

test('arrayToList -> listToArray roundtrip: strings', () => {
  const original = ['hello', 'world', ''];
  const list = arrayToList(original);
  const result = listToArray(list);
  assert(result.items.length === 3);
  assert(result.items[0] === 'hello');
  assert(result.items[2] === '', 'empty string preserved');
});

test('arrayToList -> listToArray roundtrip: 1000 elements', () => {
  const original = Array.from({length: 1000}, (_, i) => i);
  const list = arrayToList(original);
  const result = listToArray(list);
  assert(result.items.length === 1000, `expected 1000, got ${result.items.length}`);
  assert(result.items[0] === 0);
  assert(result.items[999] === 999);
});

// =====================================================================
// 16. FUZZ numberToNat / natToNumber roundtrip
// =====================================================================

test('numberToNat -> natToNumber roundtrip: 0', () => {
  const nat = numberToNat(0);
  assert(natToNumber(nat) === 0, 'roundtrip 0');
});

test('numberToNat -> natToNumber roundtrip: 1', () => {
  const nat = numberToNat(1);
  assert(natToNumber(nat) === 1, 'roundtrip 1');
});

test('numberToNat -> natToNumber roundtrip: 100', () => {
  const nat = numberToNat(100);
  assert(natToNumber(nat) === 100, 'roundtrip 100');
});

test('numberToNat -> natToNumber roundtrip: negative clamped to 0', () => {
  const nat = numberToNat(-5);
  const result = natToNumber(nat);
  assert(result === 0, `negative should clamp, got ${result}`);
});

// =====================================================================
// 17. FUZZ mixed Scott-encoding formats (object vs function)
// =====================================================================

test('matchOr: object-format Scott value', () => {
  // Object-format: { ctor: (cases) => cases.ctor(slots...) }
  const objScott = { just: (c) => c.just(42) };
  const result = matchOr(objScott, { just: (x) => x * 2, nothing: () => 0 }, -1);
  // matchOr should handle object-format
  assert(typeof result === 'number', `should return number, got ${typeof result}`);
});

test('probe: object-format Scott value', () => {
  const objScott = { pair: (c) => c.pair('a', 'b') };
  const result = probe(objScott);
  if (result !== null) {
    assert(result.ctor === 'pair', `expected pair, got ${result.ctor}`);
    assert(result.slots.length === 2);
  }
  // null is also acceptable if object-format not supported by probe
});

test('getCtor: object-format vs function-format', () => {
  const funcScott = construct('left', 42);
  const ctorFunc = getCtor(funcScott);
  assert(ctorFunc === 'left', 'function-format getCtor');

  // Object-format
  const objScott = { left: (c) => c.left(42) };
  const ctorObj = getCtor(objScott);
  if (ctorObj !== null) {
    assert(ctorObj === 'left', `object-format getCtor should return "left", got "${ctorObj}"`);
  }
});

test('deepEqual: mixed format comparison', () => {
  const func = construct('pair', 1, 2);
  const other = construct('pair', 1, 2);
  assert(deepEqual(func, other, 0), 'same format should be equal');
});

// =====================================================================
// 18. FUZZ construct edge cases
// =====================================================================

test('construct: nullary constructor', () => {
  const val = construct('nothing');
  const probed = probe(val);
  assert(probed !== null);
  assert(probed.ctor === 'nothing');
  assert(probed.slots.length === 0);
});

test('construct: 10 slots', () => {
  const val = construct('big', 1, 2, 3, 4, 5, 6, 7, 8, 9, 10);
  const probed = probe(val);
  assert(probed !== null);
  assert(probed.ctor === 'big');
  assert(probed.slots.length === 10);
  assert(probed.slots[9] === 10);
});

test('construct: special character constructor name', () => {
  const val = construct('_∷_', 'head', 'tail');
  const probed = probe(val);
  assert(probed !== null);
  assert(probed.ctor === '_∷_');
});

// =====================================================================
// 19. PROPERTY: deepEqual(x, x) === true (reflexivity)
// =====================================================================

test('deepEqual reflexivity: number', () => {
  for (const x of [0, -0, 1, -1, NaN, Infinity, -Infinity, 3.14, Number.MAX_SAFE_INTEGER]) {
    assert(deepEqual(x, x, 0), `deepEqual(${x}, ${x}) should be true`);
  }
});

test('deepEqual reflexivity: string', () => {
  for (const x of ['', 'hello', '\u0000', 'a'.repeat(10000)]) {
    assert(deepEqual(x, x, 0), `deepEqual(string, string) should be true`);
  }
});

test('deepEqual reflexivity: null and undefined', () => {
  assert(deepEqual(null, null, 0), 'null');
  assert(deepEqual(undefined, undefined, 0), 'undefined');
});

test('deepEqual reflexivity: Scott-encoded values', () => {
  const vals = [
    construct('nothing'),
    construct('just', 42),
    construct('pair', NaN, Infinity),
    construct('nested', construct('inner', 'x')),
    construct('deep', construct('a', construct('b', construct('c')))),
  ];
  for (const x of vals) {
    assert(deepEqual(x, x, 0), `deepEqual(Scott, Scott) reflexivity failed`);
  }
});

test('deepEqual reflexivity: BigInt and boolean', () => {
  assert(deepEqual(42n, 42n, 0), 'BigInt');
  assert(deepEqual(true, true, 0), 'true');
  assert(deepEqual(false, false, 0), 'false');
});

// =====================================================================
// 20. PROPERTY: deepEqual(x, y) === deepEqual(y, x) (symmetry)
// =====================================================================

test('deepEqual symmetry: primitives', () => {
  const pairs = [
    [1, 2], [1, 1], ['a', 'b'], [null, undefined], [0, -0],
    [NaN, NaN], [true, false], [42n, 43n], [42n, 42n],
  ];
  for (const [a, b] of pairs) {
    const ab = deepEqual(a, b, 0);
    const ba = deepEqual(b, a, 0);
    assert(ab === ba, `symmetry: deepEqual(${a}, ${b})=${ab} but deepEqual(${b}, ${a})=${ba}`);
  }
});

test('deepEqual symmetry: Scott-encoded values', () => {
  const pairs = [
    [construct('left', 1), construct('right', 1)],
    [construct('pair', 1, 2), construct('pair', 1, 2)],
    [construct('pair', 1, 2), construct('pair', 2, 1)],
    [construct('just', NaN), construct('just', NaN)],
    [construct('a'), construct('b')],
    [construct('x', 1, 2), construct('x', 1)],
  ];
  for (const [a, b] of pairs) {
    const ab = deepEqual(a, b, 0);
    const ba = deepEqual(b, a, 0);
    assert(ab === ba, `symmetry: deepEqual(Scott, Scott) mismatch`);
  }
});

test('deepEqual symmetry: cross-type', () => {
  const pairs = [
    [construct('x'), null],
    [construct('x'), 42],
    [null, construct('x')],
    [42, construct('x')],
  ];
  for (const [a, b] of pairs) {
    const ab = deepEqual(a, b, 0);
    const ba = deepEqual(b, a, 0);
    assert(ab === ba, `symmetry: cross-type deepEqual mismatch`);
  }
});

// =====================================================================
// 21. PROPERTY: cloneSlot(wrapMutable(x)) deep-equals x
// =====================================================================

test('cloneSlot(wrapMutable(x)) deep-equals x: primitives in Scott', () => {
  const vals = [
    construct('rec', 42),
    construct('rec', 'hello'),
    construct('rec', true),
    construct('rec', null),
    construct('rec', 3.14),
  ];
  for (const x of vals) {
    const wrapped = wrapMutable(x);
    const cloned = cloneSlot(wrapped);
    assert(deepEqual(cloned, x, 0), 'cloneSlot(wrapMutable(x)) should deep-equal x');
  }
});

test('cloneSlot(wrapMutable(x)) deep-equals x: nested Scott values', () => {
  const inner = construct('inner', 1, 2);
  const outer = construct('outer', inner, 'x');
  const wrapped = wrapMutable(outer);
  const cloned = cloneSlot(wrapped);
  assert(deepEqual(cloned, outer, 0), 'nested Scott clone should deep-equal original');
});

test('cloneSlot(wrapMutable(x)) deep-equals x: deeply nested', () => {
  let val = construct('leaf', 42);
  for (let i = 0; i < 10; i++) {
    val = construct('node', val);
  }
  const wrapped = wrapMutable(val);
  const cloned = cloneSlot(wrapped);
  assert(deepEqual(cloned, val, 0), 'deeply nested clone should deep-equal original');
});

test('cloneSlot(wrapMutable(x)) deep-equals x: multiple slots', () => {
  const val = construct('record', 1, 'two', construct('three'), true, 42n);
  const wrapped = wrapMutable(val);
  const cloned = cloneSlot(wrapped);
  // Verify structure matches
  const origSlots = getSlots(val);
  const cloneSlots = getSlots(cloned);
  assert(origSlots.length === cloneSlots.length, 'slot count should match');
  assert(cloneSlots[0] === 1, 'slot 0');
  assert(cloneSlots[1] === 'two', 'slot 1');
  assert(cloneSlots[3] === true, 'slot 3');
});

test('cloneSlot(wrapMutable(x)) deep-equals x: nullary constructor', () => {
  const val = construct('nothing');
  const wrapped = wrapMutable(val);
  const cloned = cloneSlot(wrapped);
  assert(deepEqual(cloned, val, 0), 'nullary constructor clone should deep-equal original');
});

// =====================================================================
// 22. PROPERTY: listToArray(arrayToList(arr)) roundtrip identity
// =====================================================================

test('listToArray(arrayToList(arr)) roundtrip: random int arrays', () => {
  const testArrays = [
    [],
    [0],
    [1, 2, 3, 4, 5],
    [-1, 0, 1],
    Array.from({length: 100}, (_, i) => i * 7),
    [NaN, Infinity, -Infinity, -0],
  ];
  for (const arr of testArrays) {
    const result = listToArray(arrayToList(arr));
    assert(!result.incomplete, 'should be complete');
    assert(result.items.length === arr.length, `length ${result.items.length} !== ${arr.length}`);
    for (let i = 0; i < arr.length; i++) {
      if (Number.isNaN(arr[i])) {
        assert(Number.isNaN(result.items[i]), `element ${i} should be NaN`);
      } else {
        assert(Object.is(result.items[i], arr[i]), `element ${i}: ${result.items[i]} !== ${arr[i]}`);
      }
    }
  }
});

test('listToArray(arrayToList(arr)) roundtrip: mixed types', () => {
  const arr = ['hello', 42, true, null, undefined, 99n, construct('just', 1)];
  const result = listToArray(arrayToList(arr));
  assert(result.items.length === arr.length, 'length should match');
  assert(result.items[0] === 'hello');
  assert(result.items[1] === 42);
  assert(result.items[2] === true);
  assert(result.items[3] === null);
  assert(result.items[4] === undefined);
  assert(result.items[5] === 99n);
});

test('listToArray(arrayToList(arr)) roundtrip: single element', () => {
  for (const x of [0, '', false, null, undefined]) {
    const result = listToArray(arrayToList([x]));
    assert(result.items.length === 1, 'single element array');
    assert(result.items[0] === x, `single element: ${result.items[0]} !== ${x}`);
  }
});

// =====================================================================
// 23. PROPERTY: ensureString/ensureNumber with every JS type
// =====================================================================

test('ensureString: every JS type', () => {
  hush();
  try {
    const values = [
      42n,                          // BigInt
      Symbol('test'),               // Symbol
      new Proxy({}, {}),            // Proxy
      null,
      undefined,
      { toString() { throw new Error('boom'); } },  // throwing toString
      true,
      false,
      0,
      '',
      'hello',
      NaN,
      Infinity,
      -Infinity,
      [],
      {},
      () => {},
      new Date(),
      /regex/,
      new Map(),
      new Set(),
    ];
    for (const v of values) {
      const result = ensureString(v);
      assert(typeof result === 'string', `ensureString should return string for ${typeof v}, got ${typeof result}`);
    }
  } finally { unhush(); }
});

test('ensureNumber: every JS type', () => {
  hush();
  try {
    const values = [
      42n,                          // BigInt
      null,
      undefined,
      true,
      false,
      0,
      '',
      'hello',
      NaN,
      Infinity,
      -Infinity,
      [],
      {},
      () => {},
      new Date(),
      /regex/,
      new Map(),
      new Set(),
    ];
    for (const v of values) {
      const result = ensureNumber(v);
      assert(typeof result === 'number', `ensureNumber should return number for ${typeof v}, got ${typeof result}`);
    }
  } finally { unhush(); }
});

test('ensureNumber: Symbol does not crash', () => {
  hush();
  try {
    const result = ensureNumber(Symbol('test'));
    assert(typeof result === 'number', 'Symbol should produce a number');
  } finally { unhush(); }
});

test('ensureNumber: Proxy does not crash', () => {
  hush();
  try {
    const result = ensureNumber(new Proxy({}, {}));
    assert(typeof result === 'number', 'Proxy should produce a number');
  } finally { unhush(); }
});

test('ensureString: object with throwing toString', () => {
  const obj = { toString() { throw new Error('toString bomb'); } };
  const result = ensureString(obj);
  assert(typeof result === 'string', 'should still return a string');
});

test('ensureNumber: object with throwing valueOf', () => {
  hush();
  try {
    const obj = { valueOf() { throw new Error('valueOf bomb'); } };
    const result = ensureNumber(obj);
    assert(typeof result === 'number', 'should still return a number');
  } finally { unhush(); }
});

// =====================================================================
// serializeEvent fuzz tests
// =====================================================================

// Replicate serializeEvent from reactive.js (unexported closure)
function serializeEvent(event) {
  if (!event) return 'null';
  const cases = {
    never: () => 'never',
    sub: (subEvent) => `sub(${serializeEvent(subEvent)})`,
    interval: (ms, msg) => `interval(${ms})`,
    timeout: (ms, msg) => `timeout(${ms})`,
    animationFrame: (msg) => 'animationFrame',
    animationFrameWithTime: (handler) => 'animationFrameWithTime',
    springLoop: (cfg, onTick, onSettled) => {
      let pos, vel, tgt, stiff, damp;
      cfg({ mkSpringConfig: (p, v, t, s, d) => { pos = p; vel = v; tgt = t; stiff = s; damp = d; } });
      return `springLoop(${pos},${vel},${tgt},${stiff},${damp})`;
    },
    onKeyDown: (handler) => 'onKeyDown',
    onKeyUp: (handler) => 'onKeyUp',
    onMouseDown: (handler) => 'onMouseDown',
    onMouseUp: (handler) => 'onMouseUp',
    onMouseMove: (handler) => 'onMouseMove',
    onClick: (handler) => 'onClick',
    onKeys: (pairs) => {
      const pairArray = listToArray(pairs).items;
      const keys = [];
      for (const pair of pairArray) {
        let k;
        try {
          if (typeof pair === 'function') {
            pair({ '_,_': (a) => { k = a; } });
          } else if (pair && typeof pair['_,_'] === 'function') {
            pair['_,_']({ '_,_': (a) => { k = a; } });
          }
        } catch { /* ignore */ }
        if (k !== undefined) keys.push(k);
      }
      return `onKeys(${keys.join(',')})`;
    },
    httpGet: (url, ok, err) => `httpGet(${url})`,
    httpPost: (url, body, ok, err) => `httpPost(${url})`,
    merge: (e1, e2) => `merge(${serializeEvent(e1)},${serializeEvent(e2)})`,
    debounce: (ms, inner) => `debounce(${ms},${serializeEvent(inner)})`,
    throttle: (ms, inner) => `throttle(${ms},${serializeEvent(inner)})`,
    wsConnect: (url, handler) => `wsConnect(${url})`,
    onUrlChange: (handler) => 'onUrlChange',
    worker: (url, input) => `worker(${url},${input})`,
    workerWithProgress: (url, input) => `workerWithProgress(${url},${input})`,
    parallel: (_typeB, eventList, mapFn) => 'parallel',
    race: (eventList) => 'race',
    poolWorker: (poolSize, url, input) => `poolWorker(${poolSize},${url},${input})`,
    poolWorkerWithProgress: (poolSize, url, input) => `poolWorkerWithProgress(${poolSize},${url},${input})`,
    workerChannel: (url) => `workerChannel(${url})`,
    allocShared: (n) => `allocShared(${n})`,
    workerShared: (buf, url, input) => `workerShared(${url},${input})`,
    allocImage: (w, h) => `allocImage(${w},${h})`,
    allocBuffer: (n) => `allocBuffer(${n})`,
    foldE: (_typeB, init, step, inner) => `foldE(${serializeEvent(inner)})`,
    mapFilterE: (_typeB, f, inner) => `mapFilterE(${serializeEvent(inner)})`,
    switchE: (initial, meta) => `switchE(${serializeEvent(initial)},${serializeEvent(meta)})`
  };
  const proxy = new Proxy(cases, {
    get: (target, prop) => target[prop] || ((...args) => {
      return `unknown(${String(prop)})`;
    })
  });
  return event(proxy);
}

// --- serializeEvent: all Event constructors produce string fingerprints ---

test('serializeEvent: never', () => {
  const event = (c) => c.never();
  const fp = serializeEvent(event);
  assert(typeof fp === 'string', 'fingerprint should be a string');
  assert(fp === 'never', `expected 'never', got '${fp}'`);
});

test('serializeEvent: sub wraps inner event', () => {
  const inner = (c) => c.never();
  const event = (c) => c.sub(inner);
  const fp = serializeEvent(event);
  assert(typeof fp === 'string', 'fingerprint should be a string');
  assert(fp === 'sub(never)', `expected 'sub(never)', got '${fp}'`);
});

test('serializeEvent: merge combines two events', () => {
  const e1 = (c) => c.never();
  const e2 = (c) => c.onClick(() => {});
  const event = (c) => c.merge(e1, e2);
  const fp = serializeEvent(event);
  assert(typeof fp === 'string', 'fingerprint should be a string');
  assert(fp === 'merge(never,onClick)', `expected 'merge(never,onClick)', got '${fp}'`);
});

test('serializeEvent: debounce wraps inner', () => {
  const inner = (c) => c.onKeyDown(() => {});
  const event = (c) => c.debounce(300, inner);
  const fp = serializeEvent(event);
  assert(fp === 'debounce(300,onKeyDown)', `expected 'debounce(300,onKeyDown)', got '${fp}'`);
});

test('serializeEvent: throttle wraps inner', () => {
  const inner = (c) => c.onMouseMove(() => {});
  const event = (c) => c.throttle(100, inner);
  const fp = serializeEvent(event);
  assert(fp === 'throttle(100,onMouseMove)', `expected 'throttle(100,onMouseMove)', got '${fp}'`);
});

test('serializeEvent: foldE uses inner event fingerprint', () => {
  const inner = (c) => c.onClick(() => {});
  const event = (c) => c.foldE(null, 0, (x) => (s) => s + x, inner);
  const fp = serializeEvent(event);
  assert(fp === 'foldE(onClick)', `expected 'foldE(onClick)', got '${fp}'`);
});

test('serializeEvent: mapFilterE uses inner event fingerprint', () => {
  const inner = (c) => c.onKeyUp(() => {});
  const event = (c) => c.mapFilterE(null, (x) => x, inner);
  const fp = serializeEvent(event);
  assert(fp === 'mapFilterE(onKeyUp)', `expected 'mapFilterE(onKeyUp)', got '${fp}'`);
});

test('serializeEvent: switchE uses both event fingerprints', () => {
  const initial = (c) => c.never();
  const meta = (c) => c.onClick(() => {});
  const event = (c) => c.switchE(initial, meta);
  const fp = serializeEvent(event);
  assert(fp === 'switchE(never,onClick)', `expected 'switchE(never,onClick)', got '${fp}'`);
});

test('serializeEvent: parallel returns fixed string', () => {
  const event = (c) => c.parallel(null, [], () => {});
  const fp = serializeEvent(event);
  assert(fp === 'parallel', `expected 'parallel', got '${fp}'`);
});

test('serializeEvent: race returns fixed string', () => {
  const event = (c) => c.race([]);
  const fp = serializeEvent(event);
  assert(fp === 'race', `expected 'race', got '${fp}'`);
});

test('serializeEvent: interval', () => {
  const event = (c) => c.interval(1000, 'tick');
  const fp = serializeEvent(event);
  assert(fp === 'interval(1000)', `expected 'interval(1000)', got '${fp}'`);
});

test('serializeEvent: timeout', () => {
  const event = (c) => c.timeout(500, 'done');
  const fp = serializeEvent(event);
  assert(fp === 'timeout(500)', `expected 'timeout(500)', got '${fp}'`);
});

test('serializeEvent: animationFrame', () => {
  const event = (c) => c.animationFrame(() => {});
  const fp = serializeEvent(event);
  assert(fp === 'animationFrame', `expected 'animationFrame', got '${fp}'`);
});

test('serializeEvent: httpGet', () => {
  const event = (c) => c.httpGet('/api/data', () => {}, () => {});
  const fp = serializeEvent(event);
  assert(fp === 'httpGet(/api/data)', `expected 'httpGet(/api/data)', got '${fp}'`);
});

test('serializeEvent: httpPost', () => {
  const event = (c) => c.httpPost('/api/submit', '{}', () => {}, () => {});
  const fp = serializeEvent(event);
  assert(fp === 'httpPost(/api/submit)', `expected 'httpPost(/api/submit)', got '${fp}'`);
});

test('serializeEvent: wsConnect', () => {
  const event = (c) => c.wsConnect('ws://localhost:8080', () => {});
  const fp = serializeEvent(event);
  assert(fp === 'wsConnect(ws://localhost:8080)', `expected wsConnect fingerprint, got '${fp}'`);
});

test('serializeEvent: onUrlChange', () => {
  const event = (c) => c.onUrlChange(() => {});
  const fp = serializeEvent(event);
  assert(fp === 'onUrlChange', `expected 'onUrlChange', got '${fp}'`);
});

test('serializeEvent: worker', () => {
  const event = (c) => c.worker('worker.js', 'input');
  const fp = serializeEvent(event);
  assert(fp === 'worker(worker.js,input)', `expected worker fingerprint, got '${fp}'`);
});

test('serializeEvent: springLoop', () => {
  const cfg = (c) => c.mkSpringConfig(0, 0, 100, 170, 26);
  const event = (c) => c.springLoop(cfg, () => {}, () => {});
  const fp = serializeEvent(event);
  assert(fp === 'springLoop(0,0,100,170,26)', `expected springLoop fingerprint, got '${fp}'`);
});

test('serializeEvent: allocShared', () => {
  const event = (c) => c.allocShared(1024);
  const fp = serializeEvent(event);
  assert(fp === 'allocShared(1024)', `expected 'allocShared(1024)', got '${fp}'`);
});

test('serializeEvent: allocImage', () => {
  const event = (c) => c.allocImage(800, 600);
  const fp = serializeEvent(event);
  assert(fp === 'allocImage(800,600)', `expected 'allocImage(800,600)', got '${fp}'`);
});

test('serializeEvent: allocBuffer', () => {
  const event = (c) => c.allocBuffer(4096);
  const fp = serializeEvent(event);
  assert(fp === 'allocBuffer(4096)', `expected 'allocBuffer(4096)', got '${fp}'`);
});

// --- serializeEvent: null/falsy input ---

test('serializeEvent: null event returns "null"', () => {
  assert(serializeEvent(null) === 'null', 'null should serialize to "null"');
  assert(serializeEvent(undefined) === 'null', 'undefined should serialize to "null"');
  assert(serializeEvent(false) === 'null', 'false should serialize to "null"');
  assert(serializeEvent(0) === 'null', '0 should serialize to "null"');
  assert(serializeEvent('') === 'null', 'empty string should serialize to "null"');
});

// --- serializeEvent: unknown constructor triggers Proxy fallback ---

test('serializeEvent: unknown constructor uses Proxy fallback', () => {
  hush();
  try {
    const event = (c) => c.totallyNewConstructor(1, 2, 3);
    const fp = serializeEvent(event);
    assert(typeof fp === 'string', 'fingerprint should be a string');
    assert(fp === 'unknown(totallyNewConstructor)', `expected unknown fallback, got '${fp}'`);
  } finally { unhush(); }
});

// --- serializeEvent: DOM events with throwing getters ---

test('serializeEvent: non-function truthy value throws (not silently handled)', () => {
  // serializeEvent only guards against falsy values. A truthy non-function
  // (like a DOM event object) will throw when called as event(proxy).
  // This documents the actual behavior — callers must ensure they pass functions.
  const domEvent = {};
  Object.defineProperty(domEvent, 'type', {
    get() { throw new Error('SecurityError: blocked'); }
  });
  let threw = false;
  try {
    serializeEvent(domEvent);
  } catch (e) {
    threw = true;
    assert(e instanceof TypeError, `expected TypeError, got ${e.constructor.name}`);
  }
  assert(threw, 'truthy non-function should throw TypeError');
});

test('serializeEvent: function that throws when called', () => {
  const badEvent = () => { throw new TypeError('Cannot read properties'); };
  let threw = false;
  try {
    serializeEvent(badEvent);
  } catch (e) {
    threw = true;
  }
  // serializeEvent does not try/catch internally, so a throwing event propagates
  assert(threw, 'throwing event function should propagate the error');
});

test('serializeEvent: event function calling a non-existent constructor via Proxy', () => {
  hush();
  try {
    // Simulates a future Event constructor not yet in the cases object
    const futureEvent = (c) => c.futureWebTransport('url', () => {});
    const fp = serializeEvent(futureEvent);
    assert(fp === 'unknown(futureWebTransport)', `expected unknown fallback, got '${fp}'`);
  } finally { unhush(); }
});

// --- Proxy fallback edge cases ---

test('Proxy fallback: handler returning empty string, 0, null, false, undefined', () => {
  // The Proxy uses `target[prop] || fallback`. Since target[prop] is a function
  // reference (always truthy), the fallback only triggers for missing keys.
  // But if someone puts a non-function falsy value in the cases object, || would trigger.
  const cases = {
    emptyStr: '',     // falsy
    zero: 0,          // falsy
    nullVal: null,     // falsy
    falseVal: false,   // falsy
    undefVal: undefined, // falsy
    goodFn: () => 'ok', // truthy function
  };
  const proxy = new Proxy(cases, {
    get: (target, prop) => target[prop] || ((...args) => `fallback(${String(prop)})`)
  });

  // Falsy values cause fallback to trigger — this is the known || behavior
  assert(typeof proxy.emptyStr === 'function', 'empty string triggers fallback function');
  assert(proxy.emptyStr() === 'fallback(emptyStr)', 'empty string falls back');
  assert(typeof proxy.zero === 'function', '0 triggers fallback function');
  assert(proxy.zero() === 'fallback(zero)', '0 falls back');
  assert(typeof proxy.nullVal === 'function', 'null triggers fallback function');
  assert(proxy.nullVal() === 'fallback(nullVal)', 'null falls back');
  assert(typeof proxy.falseVal === 'function', 'false triggers fallback function');
  assert(proxy.falseVal() === 'fallback(falseVal)', 'false falls back');
  assert(typeof proxy.undefVal === 'function', 'undefined triggers fallback function');
  assert(proxy.undefVal() === 'fallback(undefVal)', 'undefined falls back');

  // Truthy function does NOT trigger fallback
  assert(proxy.goodFn() === 'ok', 'truthy function does not fall back');
});

test('Proxy fallback: Symbol and numeric property access', () => {
  const cases = { known: () => 'ok' };
  const proxy = new Proxy(cases, {
    get: (target, prop) => target[prop] || ((...args) => `fallback(${String(prop)})`)
  });
  // Symbol access
  const sym = Symbol('test');
  assert(typeof proxy[sym] === 'function', 'Symbol property triggers fallback');
  assert(proxy[sym]() === 'fallback(Symbol(test))', 'Symbol property falls back correctly');
});

// --- Fingerprint stability: same input produces same fingerprint ---

test('serializeEvent: fingerprint stability — same event always same fingerprint', () => {
  const events = [
    (c) => c.never(),
    (c) => c.onClick(() => {}),
    (c) => c.interval(1000, 'tick'),
    (c) => c.merge((c2) => c2.never(), (c2) => c2.onClick(() => {})),
    (c) => c.debounce(300, (c2) => c2.onKeyDown(() => {})),
    (c) => c.foldE(null, 0, (x) => (s) => s + x, (c2) => c2.onClick(() => {})),
    (c) => c.switchE((c2) => c2.never(), (c2) => c2.onClick(() => {})),
    (c) => c.httpGet('/api', () => {}, () => {}),
    (c) => c.wsConnect('ws://localhost', () => {}),
    (c) => c.parallel(null, [], () => {}),
    (c) => c.race([]),
  ];

  for (const event of events) {
    const fp1 = serializeEvent(event);
    const fp2 = serializeEvent(event);
    const fp3 = serializeEvent(event);
    assert(fp1 === fp2, `fingerprint should be stable: '${fp1}' !== '${fp2}'`);
    assert(fp2 === fp3, `fingerprint should be stable across 3 calls: '${fp2}' !== '${fp3}'`);
    assert(typeof fp1 === 'string', `fingerprint should be a string, got ${typeof fp1}`);
    assert(fp1.length > 0, 'fingerprint should be non-empty');
  }
});

test('serializeEvent: different events produce different fingerprints', () => {
  const events = [
    (c) => c.never(),
    (c) => c.onClick(() => {}),
    (c) => c.interval(1000, 'tick'),
    (c) => c.interval(2000, 'tick'),
    (c) => c.httpGet('/a', () => {}, () => {}),
    (c) => c.httpGet('/b', () => {}, () => {}),
    (c) => c.debounce(100, (c2) => c2.onClick(() => {})),
    (c) => c.debounce(200, (c2) => c2.onClick(() => {})),
  ];

  const fingerprints = events.map(e => serializeEvent(e));
  const unique = new Set(fingerprints);
  assert(unique.size === fingerprints.length,
    `expected ${fingerprints.length} unique fingerprints, got ${unique.size}: [${fingerprints.join(', ')}]`);
});

test('serializeEvent: deeply nested merge tree', () => {
  // Build merge(merge(merge(never, never), never), never) — 10 levels deep
  let event = (c) => c.never();
  for (let i = 0; i < 10; i++) {
    const inner = event;
    event = (c) => c.merge(inner, (c2) => c2.never());
  }
  const fp = serializeEvent(event);
  assert(typeof fp === 'string', 'deeply nested merge should produce a string');
  assert(fp.length > 0, 'deeply nested merge fingerprint should be non-empty');
  // Verify stability
  assert(fp === serializeEvent(event), 'deeply nested merge fingerprint should be stable');
});

test('serializeEvent: deeply nested foldE/mapFilterE/switchE chain', () => {
  let event = (c) => c.onClick(() => {});
  event = ((inner) => (c) => c.foldE(null, 0, () => {}, inner))(event);
  event = ((inner) => (c) => c.mapFilterE(null, (x) => x, inner))(event);
  event = ((initial) => (c) => c.switchE(initial, (c2) => c2.never()))(event);
  const fp = serializeEvent(event);
  assert(typeof fp === 'string', 'chained combinators should produce a string');
  assert(fp === 'switchE(mapFilterE(foldE(onClick)),never)',
    `expected chained fingerprint, got '${fp}'`);
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
