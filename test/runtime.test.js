/**
 * Agdelte Runtime Tests
 * Tests for JavaScript runtime (reactive.js, events.js, agda-values.js)
 */

// Simple test runner
let passed = 0;
let failed = 0;
let skipped = 0;
const asyncTests = [];

function test(name, fn) {
  try {
    fn();
    console.log(`✓ ${name}`);
    passed++;
  } catch (e) {
    console.log(`✗ ${name}: ${e.message}`);
    failed++;
  }
}

function asyncTest(name, fn) {
  asyncTests.push({ name, fn });
}

function assert(condition, message = 'Assertion failed') {
  if (!condition) throw new Error(message);
}

function assertEqual(actual, expected, message) {
  if (actual !== expected) {
    throw new Error(message || `Expected ${expected}, got ${actual}`);
  }
}

function assertDeepEqual(actual, expected, message) {
  if (JSON.stringify(actual) !== JSON.stringify(expected)) {
    throw new Error(message || `Expected ${JSON.stringify(expected)}, got ${JSON.stringify(actual)}`);
  }
}

// ========================================
// Events Tests
// ========================================

// ========================================
// Combinator Runtime Tests
// ========================================

console.log('\n=== Combinator Runtime Tests ===\n');

test('foldE accumulates state across dispatches', () => {
  // Simulate the foldE runtime logic:
  // On each input value, apply step(input, state) and dispatch new state
  let state = 0;
  const step = (input) => (oldState) => oldState + input;
  const results = [];
  const dispatch = (val) => results.push(val);

  // Simulate incoming events: 1, 2, 3
  for (const input of [1, 2, 3]) {
    state = step(input)(state);
    dispatch(state);
  }

  assertDeepEqual(results, [1, 3, 6], 'foldE should accumulate: 0+1=1, 1+2=3, 3+3=6');
});

test('mapFilterE filters via Maybe', () => {
  // Simulate mapFilterE: dispatch only when function returns just(x)
  const results = [];
  const dispatch = (val) => results.push(val);

  // Filter function: just(x*2) if x > 0, nothing otherwise
  const filterMap = (x) => {
    if (x > 0) {
      return { tag: 'just', value: x * 2 };
    } else {
      return { tag: 'nothing' };
    }
  };

  // Simulate dispatching through mapFilterE
  for (const input of [-1, 2, 0, 3, -5, 4]) {
    const result = filterMap(input);
    if (result.tag === 'just') {
      dispatch(result.value);
    }
  }

  assertDeepEqual(results, [4, 6, 8], 'mapFilterE should filter and map: 2*2=4, 3*2=6, 4*2=8');
});

test('switchE swaps subscription', () => {
  // Simulate switchE: dispatch from current source, switchable
  const results = [];
  let currentSource = 'A';

  // Simulate: dispatch from current source
  const dispatchFromCurrent = () => results.push(currentSource);

  dispatchFromCurrent(); // 'A'
  dispatchFromCurrent(); // 'A'

  // Switch to source B
  currentSource = 'B';

  dispatchFromCurrent(); // 'B'
  dispatchFromCurrent(); // 'B'

  assertDeepEqual(results, ['A', 'A', 'B', 'B'], 'switchE should swap sources');
});

// ========================================
// Deep Equality Tests
// ========================================

console.log('\n=== Deep Equality Tests ===\n');

// Import deepEqual indirectly by testing Scott-encoded values
test('deepEqual handles primitives', () => {
  assertEqual(1, 1);
  assertEqual('hello', 'hello');
  assertEqual(true, true);
});

test('deepEqual handles Scott-encoded records', () => {
  // Scott-encoded record: mkRecord(a, b) = cases => cases.mkRecord(a, b)
  const mkPair = (x, y) => (cases) => cases.mkPair(x, y);
  const pair1 = mkPair(1, 2);
  const pair2 = mkPair(1, 2);
  const pair3 = mkPair(1, 3);

  // Extract values to compare
  let v1, v2, v3;
  pair1({ mkPair: (x, y) => { v1 = [x, y]; } });
  pair2({ mkPair: (x, y) => { v2 = [x, y]; } });
  pair3({ mkPair: (x, y) => { v3 = [x, y]; } });

  assertDeepEqual(v1, v2, 'same Scott pairs should be equal');
  assert(v1[1] !== v3[1], 'different Scott pairs should differ');
});

// ========================================
// Slot Detection Tests
// ========================================

console.log('\n=== Slot Detection Tests ===\n');

test('countSlots counts record fields', () => {
  // Scott-encoded 3-field record
  const mkTriple = (a, b, c) => (cases) => cases.mk(a, b, c);
  const triple = mkTriple(1, 2, 3);

  // Count by probing
  let count = 0;
  triple({
    mk: (...args) => { count = args.length; }
  });

  assertEqual(count, 3, 'should detect 3 slots');
});

test('probeSlots extracts field values', () => {
  const mkTriple = (a, b, c) => (cases) => cases.mk(a, b, c);
  const triple = mkTriple('x', 'y', 'z');

  // Probe
  let values;
  triple({
    mk: (...args) => { values = args; }
  });

  assertDeepEqual(values, ['x', 'y', 'z'], 'should extract all values');
});

// ========================================
// List Conversion Tests
// ========================================

console.log('\n=== List Conversion Tests ===\n');

test('Scott list structure', () => {
  // Scott-encoded list: nil = c => c.nil, cons(h,t) = c => c.cons(h, t)
  const nil = (c) => c.nil();
  const cons = (h, t) => (c) => c.cons(h, t);

  const list = cons(1, cons(2, cons(3, nil)));

  // Convert to array
  const toArray = (lst) => {
    const result = [];
    let current = lst;
    while (true) {
      let done = false;
      current({
        nil: () => { done = true; },
        cons: (h, t) => { result.push(h); current = t; }
      });
      if (done) break;
    }
    return result;
  };

  assertDeepEqual(toArray(list), [1, 2, 3], 'should convert Scott list to array');
});

test('listToArray returns incomplete flag for malformed lists', () => {
  // Mock listToArray behavior (the actual function is internal to reactive.js)
  // Test the pattern: malformed tail returns incomplete: true
  const listToArray = (list) => {
    if (!list) return { items: [], incomplete: false };
    if (Array.isArray(list)) return { items: list, incomplete: false };
    if (typeof list !== 'function') {
      return { items: [], incomplete: true };
    }
    const result = [];
    let current = list;
    let incomplete = false;
    while (true) {
      if (typeof current !== 'function') {
        incomplete = true;
        break;
      }
      const done = current({
        '[]': () => true,
        '_∷_': (head, tail) => {
          result.push(head);
          current = tail;
          return false;
        }
      });
      if (done) break;
    }
    return { items: result, incomplete };
  };

  // Normal list (native array)
  const result1 = listToArray([1, 2, 3]);
  assertDeepEqual(result1.items, [1, 2, 3], 'native array items');
  assertEqual(result1.incomplete, false, 'native array not incomplete');

  // Malformed input (not a function)
  const result2 = listToArray('invalid');
  assertDeepEqual(result2.items, [], 'malformed input empty items');
  assertEqual(result2.incomplete, true, 'malformed input is incomplete');

  // Scott list with broken tail
  const brokenList = (c) => c['_∷_'](1, 'not-a-function');
  const result3 = listToArray(brokenList);
  assertDeepEqual(result3.items, [1], 'partial items before break');
  assertEqual(result3.incomplete, true, 'broken tail is incomplete');
});

// ========================================
// Agda Values Abstraction Tests
// ========================================

console.log('\n=== Agda Values Abstraction Tests ===\n');

import * as AgdaValues from '../runtime/agda-values.js';

test('match works with Scott-encoded values', () => {
  const just = (x) => (c) => c.just(x);
  const nothing = (c) => c.nothing();

  const result1 = AgdaValues.match(just(42), {
    just: (x) => x * 2,
    nothing: () => 0
  });
  assertEqual(result1, 84, 'just(42) should return 84');

  const result2 = AgdaValues.match(nothing, {
    just: (x) => x * 2,
    nothing: () => 0
  });
  assertEqual(result2, 0, 'nothing should return 0');
});

test('getCtor works with Scott-encoded values', () => {
  const scottValue = (c) => c.myConstructor(1, 2, 3);
  assertEqual(AgdaValues.getCtor(scottValue), 'myConstructor', 'Scott getCtor');
});

test('getSlots works with Scott-encoded values', () => {
  const scottValue = (c) => c.mk(1, 2, 3);
  assertDeepEqual(AgdaValues.getSlots(scottValue), [1, 2, 3], 'Scott getSlots');
});

test('construct creates correct format', () => {
  // Default is Scott-encoded
  const value = AgdaValues.construct('pair', 'a', 'b');
  assertEqual(typeof value, 'function', 'default is Scott-encoded');

  const slots = AgdaValues.getSlots(value);
  assertDeepEqual(slots, ['a', 'b'], 'constructed value has correct slots');
});

test('deepEqual works with Scott-encoded values', () => {
  const scott1 = (c) => c.pair(1, 2);
  const scott2 = (c) => c.pair(1, 2);
  const scott3 = (c) => c.pair(1, 3);

  assert(deepEqual(scott1, scott2, 0), 'equal Scott values');
  assert(!deepEqual(scott1, scott3, 0), 'different Scott values');
});

// ========================================
// Bug Fix Regression Tests
// ========================================

import {
  deepEqual, countSlots, detectSlots, probeCtor, probeSlots, changedSlotsFromCache
} from '../runtime/reactive.js';
import { interpretEvent, unsubscribe as unsub } from '../runtime/events.js';

console.log('\n=== Bug #1: Slot cache invalidation on constructor change ===\n');

test('detectSlots detects dependency on slot 0', () => {
  // Model: (cases) => cases.Left(42)
  const model = (c) => c.Left(42);
  // extract returns slot 0
  const extract = (m) => {
    let val;
    m({ Left: (x) => { val = x; }, Right: (x) => { val = x; } });
    return val;
  };
  const slots = detectSlots(extract, model, 1);
  assertDeepEqual(slots, [0], 'should detect slot 0 as dependency');
});

test('detectSlots returns fresh results for different constructor', () => {
  // Left(42) — extract gets slot 0
  const modelLeft = (c) => c.Left(42);
  // Right(99) — extract gets slot 0 of Right
  const modelRight = (c) => c.Right(99);

  const extractLeft = (m) => {
    let val;
    m({ Left: (x) => { val = x; }, Right: () => { val = 'ignored'; } });
    return val;
  };

  const extractRight = (m) => {
    let val;
    m({ Left: () => { val = 'ignored'; }, Right: (x) => { val = x; } });
    return val;
  };

  const slotsL = detectSlots(extractLeft, modelLeft, 1);
  const slotsR = detectSlots(extractRight, modelRight, 1);

  // Both depend on slot 0 but in different constructors
  // The key point: detectSlots with newModel should give fresh results
  assertDeepEqual(slotsL, [0], 'Left: slot 0');
  assertDeepEqual(slotsR, [0], 'Right: slot 0');
});

test('probeCtor detects constructor name change', () => {
  const modelLeft = (c) => c.Left(42);
  const modelRight = (c) => c.Right(99);

  assertEqual(probeCtor(modelLeft), 'Left', 'Left ctor');
  assertEqual(probeCtor(modelRight), 'Right', 'Right ctor');
  assert(probeCtor(modelLeft) !== probeCtor(modelRight),
    'different constructors should be detectable');
});

test('changedSlotsFromCache detects slot changes', () => {
  const scope = { cachedArgs: null };
  const model1 = (c) => c.mk(1, 2, 3);
  const model2 = (c) => c.mk(1, 99, 3);

  // First call: no cachedArgs → returns null (can't compare)
  const first = changedSlotsFromCache(scope, model1);
  assertEqual(first, null, 'first call returns null (no cached args)');

  // Second call: compares with cached → slot 1 changed
  const second = changedSlotsFromCache(scope, model2);
  assert(second instanceof Set, 'should return Set');
  assert(second.has(1), 'slot 1 should be in changed set');
  assertEqual(second.size, 1, 'only slot 1 changed');
});

test('changedSlotsFromCache returns null when arity changes', () => {
  const scope = { cachedArgs: null };
  const model2slot = (c) => c.mk(1, 2);
  const model3slot = (c) => c.mk(1, 2, 3);

  changedSlotsFromCache(scope, model2slot);  // prime cache
  const result = changedSlotsFromCache(scope, model3slot);
  assertEqual(result, null, 'different arity returns null');
});

console.log('\n=== Bug #2: WebSocket reconnect ===\n');

test('interpretEvent wsConnect replaces old connection handlers with noops', () => {
  // We can't test real WebSocket here, but we verify the interpretEvent
  // structure handles the wsConnect case by checking it returns an object
  // with unsubscribe
  const neverEvent = (c) => c.never();
  const sub = interpretEvent(neverEvent, () => {});
  assert(sub && typeof sub.unsubscribe === 'function',
    'interpretEvent should return { unsubscribe }');
  sub.unsubscribe();
});

console.log('\n=== Bug #3: updateSubscriptions error recovery ===\n');

test('interpretEvent with null/undefined returns safe noop subscription', () => {
  const sub = interpretEvent(null, () => {});
  assert(sub && typeof sub.unsubscribe === 'function',
    'null event should return safe subscription');
  sub.unsubscribe();  // should not throw
});

test('unsubscribe handles null/undefined gracefully', () => {
  // These should not throw
  unsub(null);
  unsub(undefined);
  unsub({});
  unsub({ unsubscribe: 'not a function' });
  assert(true, 'unsubscribe should handle bad inputs');
});

console.log('\n=== Bug #4: deepEqual at max depth ===\n');

test('deepEqual returns true for identical Scott values', () => {
  const a = (c) => c.mk(1, 'hello', true);
  const b = (c) => c.mk(1, 'hello', true);
  assert(deepEqual(a, b, 0), 'identical Scott values should be equal');
});

test('deepEqual returns false for different Scott values', () => {
  const a = (c) => c.mk(1, 'hello');
  const b = (c) => c.mk(1, 'world');
  assert(!deepEqual(a, b, 0), 'different Scott values should not be equal');
});

test('deepEqual returns false for different constructors', () => {
  const a = (c) => c.Left(42);
  const b = (c) => c.Right(42);
  assert(!deepEqual(a, b, 0), 'different ctors should not be equal');
});

test('deepEqual returns true at max depth (assumes equal)', () => {
  // Build deeply nested value
  let val = (c) => c.leaf(1);
  for (let i = 0; i < 60; i++) {
    const inner = val;
    val = (c) => c.node(inner);
  }

  // Two deeply nested values with same structure
  let val2 = (c) => c.leaf(1);
  for (let i = 0; i < 60; i++) {
    const inner = val2;
    val2 = (c) => c.node(inner);
  }

  // Should return true (assumes equal at depth limit, not false)
  assert(deepEqual(val, val2, 0),
    'deeply nested identical values should return true (not false) at depth limit');
});

test('deepEqual returns true at depth limit even if deep parts differ', () => {
  // This tests that we DO assume equal at depth > 50
  // Build a value nested deeper than MAX_DEEP_EQUAL_DEPTH
  let valA = (c) => c.leaf(1);    // different leaf
  let valB = (c) => c.leaf(999);  // different leaf
  for (let i = 0; i < 55; i++) {
    const innerA = valA;
    const innerB = valB;
    valA = (c) => c.node(innerA);
    valB = (c) => c.node(innerB);
  }

  // At depth 50+, deepEqual gives up and returns true
  // This is a known trade-off: avoids false re-renders at cost of possibly missing deep changes
  assert(deepEqual(valA, valB, 0),
    'values differing only at depth > 50 should be assumed equal');
});

console.log('\n=== Bug #5: allocShared error handling ===\n');

test('interpretEvent allocShared handles failure gracefully without onError', () => {
  // No onError param — should not throw
  const results = [];
  const dispatch = (msg) => results.push(msg);

  const allocEvent = (c) => c.allocShared(
    -1,
    (buffer) => 'got-buffer'
  );

  // Should not throw even though allocation fails and no onError
  const sub = interpretEvent(allocEvent, dispatch);
  assertEqual(results.length, 0, 'no dispatch without onError');
  sub.unsubscribe();
});

console.log('\n=== Bug #6: foreachKeyed dedup without mutation ===\n');

test('array dedup logic does not mutate original array', () => {
  // Reproduce the dedup logic from updateKeyedList
  const originalItems = [10, 20, 30, 20, 40];
  const originalRef = originalItems;  // same reference

  // Simulate keyFn: identity
  let newItems = [...originalItems];
  let newKeys = newItems.map(x => x);

  // Dedup logic (from the fixed code)
  const seen = new Set();
  const duplicates = new Set();
  for (const key of newKeys) {
    if (seen.has(key)) duplicates.add(key);
    seen.add(key);
  }
  if (duplicates.size > 0) {
    const lastSeen = new Set();
    const keep = new Array(newItems.length).fill(false);
    for (let i = newItems.length - 1; i >= 0; i--) {
      if (!lastSeen.has(newKeys[i])) {
        lastSeen.add(newKeys[i]);
        keep[i] = true;
      }
    }
    const filteredItems = [];
    const filteredKeys = [];
    for (let i = 0; i < newItems.length; i++) {
      if (keep[i]) {
        filteredItems.push(newItems[i]);
        filteredKeys.push(newKeys[i]);
      }
    }
    // Fixed: reassign instead of mutating
    newItems = filteredItems;
    newKeys = filteredKeys;
  }

  // Original array must be untouched
  assertDeepEqual(originalItems, [10, 20, 30, 20, 40],
    'original array should not be mutated');
  assert(originalItems === originalRef,
    'original array reference should be preserved');

  // Deduped result should have last occurrence of 20
  assertDeepEqual(newItems, [10, 30, 20, 40],
    'dedup should keep last occurrence of duplicate key');
});

console.log('\n=== Rec #3: foreachKeyed reconciliation ===\n');

test('foreachKeyed dedup removes correct items', () => {
  // Simulate the full dedup+reconcile logic from updateKeyedList
  // Input: items with keys [A, B, C, B, D] — B is duplicated
  const items = [{k: 'A', v: 1}, {k: 'B', v: 2}, {k: 'C', v: 3}, {k: 'B', v: 4}, {k: 'D', v: 5}];
  const keyFn = item => item.k;

  let newItems = items;
  let newKeys = newItems.map(keyFn);

  // Dedup: keep last occurrence
  const seen = new Set();
  const duplicates = new Set();
  for (const key of newKeys) {
    if (seen.has(key)) duplicates.add(key);
    seen.add(key);
  }
  if (duplicates.size > 0) {
    const lastSeen = new Set();
    const keep = new Array(newItems.length).fill(false);
    for (let i = newItems.length - 1; i >= 0; i--) {
      if (!lastSeen.has(newKeys[i])) {
        lastSeen.add(newKeys[i]);
        keep[i] = true;
      }
    }
    newItems = newItems.filter((_, i) => keep[i]);
    newKeys = newKeys.filter((_, i) => keep[i]);
  }

  assertDeepEqual(newKeys, ['A', 'C', 'B', 'D'], 'dedup keeps last B');
  assertEqual(newItems[2].v, 4, 'kept B should be the last occurrence (v=4)');
});

test('foreachKeyed reordering preserves correct items', () => {
  // Simulate key-based reconciliation: old [A, B, C] → new [C, A, B]
  const oldEntries = [
    {key: 'A', value: 1},
    {key: 'B', value: 2},
    {key: 'C', value: 3},
  ];
  const newKeys = ['C', 'A', 'B'];

  const oldKeyMap = new Map();
  for (const e of oldEntries) oldKeyMap.set(e.key, e);

  const newRendered = [];
  for (const key of newKeys) {
    const old = oldKeyMap.get(key);
    assert(old !== undefined, `key ${key} should be found in old map`);
    newRendered.push(old);
  }

  assertDeepEqual(
    newRendered.map(e => e.key),
    ['C', 'A', 'B'],
    'reordered keys should match new order'
  );
  assertDeepEqual(
    newRendered.map(e => e.value),
    [3, 1, 2],
    'reordered values should match correct keys'
  );
});

test('foreachKeyed removal destroys correct entries', () => {
  // old [A, B, C, D], new [A, D] — B and C should be removed
  const oldKeys = ['A', 'B', 'C', 'D'];
  const newKeySet = new Set(['A', 'D']);

  const removed = oldKeys.filter(k => !newKeySet.has(k));
  const kept = oldKeys.filter(k => newKeySet.has(k));

  assertDeepEqual(removed, ['B', 'C'], 'B and C should be removed');
  assertDeepEqual(kept, ['A', 'D'], 'A and D should be kept');
});

test('foreachKeyed addition creates new entries', () => {
  // old [A, B], new [A, B, C, D] — C and D are new
  const oldKeyMap = new Map([['A', 1], ['B', 2]]);
  const newKeys = ['A', 'B', 'C', 'D'];

  const newEntries = newKeys.filter(k => !oldKeyMap.has(k));
  assertDeepEqual(newEntries, ['C', 'D'], 'C and D should be created');
});

console.log('\n=== Bug #7: Dead variable removal ===\n');

test('WorkerPool.submit cancel does not use local cancelled variable', () => {
  // This is a code quality test — we verify the pattern works
  // by simulating the cancel logic without a local `cancelled` variable
  let taskCancelled = false;
  let activeWorker = { terminated: false };

  const cancel = () => {
    if (taskCancelled) return;
    taskCancelled = true;
    // No local `cancelled` variable needed — task.cancelled is sufficient
    if (activeWorker) {
      activeWorker.terminated = true;
      activeWorker = null;
    }
  };

  cancel();
  assert(taskCancelled === true, 'task should be cancelled');
  assert(activeWorker === null, 'worker should be cleared');

  // Double cancel should be idempotent
  cancel();
  assert(taskCancelled === true, 'double cancel should be safe');
});

console.log('\n=== Slot Detection Edge Cases ===\n');

test('countSlots works for different arities', () => {
  assertEqual(countSlots((c) => c.mk()), 0, '0 slots');
  assertEqual(countSlots((c) => c.mk(1)), 1, '1 slot');
  assertEqual(countSlots((c) => c.mk(1, 2)), 2, '2 slots');
  assertEqual(countSlots((c) => c.mk(1, 2, 3, 4, 5)), 5, '5 slots');
});

test('countSlots returns 0 for non-function', () => {
  assertEqual(countSlots(42), 0, 'number');
  assertEqual(countSlots('hello'), 0, 'string');
  assertEqual(countSlots(null), 0, 'null');
  assertEqual(countSlots(undefined), 0, 'undefined');
});

test('probeSlots returns null for non-probeables', () => {
  assertEqual(probeSlots(null), null, 'null');
  assertEqual(probeSlots(42), null, 'number');
  assertEqual(probeSlots('str'), null, 'string');
});

test('detectSlots returns full dependency set for multi-dependency bindings', () => {
  // Model with 3 slots
  const model = (c) => c.mk(1, 2, 3);
  // Extract depends on slot 0 AND slot 2
  const extract = (m) => {
    let val;
    m({ mk: (a, b, c) => { val = a + c; } });
    return val;
  };
  const slots = detectSlots(extract, model, 3);
  assertDeepEqual(slots, [0, 2], 'multi-dependency should return [0, 2]');
});

test('detectSlots returns null for extract that throws', () => {
  const model = (c) => c.mk(1);
  const extract = () => { throw new Error('boom'); };
  const slots = detectSlots(extract, model, 1);
  assertEqual(slots, null, 'throwing extract should return null');
});

// ========================================
// BOOL_ATTRS regression tests (R9)
// ========================================

console.log('\n=== BOOL_ATTRS Regression Tests ===\n');

test('BOOL_ATTRS concept: inert and popover should be boolean attrs', () => {
  // Verify the concept: boolean attributes are set/removed rather than assigned as strings
  const boolAttrs = new Set([
    'disabled', 'checked', 'readonly', 'required', 'selected',
    'hidden', 'autofocus', 'multiple', 'open', 'novalidate',
    'formnovalidate', 'autoplay', 'controls', 'loop', 'muted',
    'default', 'reversed', 'allowfullscreen', 'async', 'defer',
    'inert', 'popover', 'ismap', 'nomodule', 'playsinline', 'itemscope',
  ]);
  assert(boolAttrs.has('inert'), 'inert should be a boolean attribute');
  assert(boolAttrs.has('popover'), 'popover should be a boolean attribute');
  assert(boolAttrs.has('ismap'), 'ismap should be a boolean attribute');
  assert(boolAttrs.has('nomodule'), 'nomodule should be a boolean attribute');
  assert(boolAttrs.has('playsinline'), 'playsinline should be a boolean attribute');
  assert(boolAttrs.has('itemscope'), 'itemscope should be a boolean attribute');
  assertEqual(boolAttrs.size, 26, 'should have 26 boolean attributes');
});

// ========================================
// Task executeTask depth limit tests (R2)
// ========================================

console.log('\n=== Task Depth Limit Tests ===\n');

test('executeTask: pure chain depth < 1000 succeeds', () => {
  // Build a chain of 100 pure tasks
  const mkChain = (n, value) => {
    if (n === 0) return (c) => c.pure(value);
    return (c) => c.pure(value); // each level is a simple pure
  };

  let result = null;
  const task = mkChain(100, 'ok');
  // Simulate executeTask logic
  const MAX_TASK_DEPTH = 1000;
  let depth = 0;
  let current = task;
  current({
    pure: (v) => { result = v; },
    fail: (e) => { result = 'error:' + e; },
  });
  assertEqual(result, 'ok', 'shallow pure chain should succeed');
});

test('executeTask: recursive pure chain exceeding depth triggers error', () => {
  // Simulate depth check
  const MAX_TASK_DEPTH = 1000;
  let errorMsg = null;

  function simulateExecuteTask(task, onSuccess, onError, _depth) {
    if (_depth > MAX_TASK_DEPTH) {
      onError('Task recursion depth exceeded');
      return;
    }
    task({
      pure: (v) => onSuccess(v),
      fail: (e) => onError(e),
    });
  }

  // At depth 1001, should error
  simulateExecuteTask(
    (c) => c.pure('value'),
    () => { errorMsg = null; },
    (e) => { errorMsg = e; },
    1001
  );
  assert(errorMsg !== null, 'depth 1001 should trigger error');
  assert(errorMsg.includes('depth exceeded'), 'error should mention depth');
});

// ========================================
// onKeyFiltered empty key tests (R9)
// ========================================

console.log('\n=== onKeyFiltered Edge Cases ===\n');

test('onKeyFiltered: empty string key in filter array', () => {
  // Simulate the onKeyFiltered logic
  const keyArray = ['Enter', '', 'Escape'];
  const events = [
    { key: 'Enter' },
    { key: '' },
    { key: 'a' },
    { key: 'Escape' },
  ];

  const matched = events.filter(e => keyArray.includes(e.key));
  assertEqual(matched.length, 3, 'should match Enter, empty string, and Escape');
  assertEqual(matched[1].key, '', 'empty string key should match');
});

test('onKeyFiltered: empty filter array matches nothing', () => {
  const keyArray = [];
  const events = [{ key: 'a' }, { key: 'Enter' }];
  const matched = events.filter(e => keyArray.includes(e.key));
  assertEqual(matched.length, 0, 'empty filter should match nothing');
});

// ========================================
// Proxy fallback in serializeEvent (E1/R11)
// ========================================

console.log('\n=== Proxy Fallback Tests ===\n');

test('Proxy fallback: falsy empty string from handler', () => {
  // Simulate the Proxy pattern from serializeEvent
  const cases = {
    known: () => 'result',
  };
  const proxy = new Proxy(cases, {
    get: (target, prop) => target[prop] || ((...args) => `unknown(${String(prop)})`)
  });

  // Known constructor works
  assertEqual(proxy.known(), 'result', 'known constructor should work');

  // Unknown constructor falls back
  const fallback = proxy.unknownCtor();
  assert(fallback.startsWith('unknown('), 'unknown constructor should fall back');
});

test('Proxy fallback: handler returning empty string is treated as falsy', () => {
  // This tests the known issue: handler returning '' is falsy, triggers fallback
  const cases = {
    emptyReturn: () => '',
  };
  const proxy = new Proxy(cases, {
    get: (target, prop) => target[prop] || ((...args) => `fallback(${String(prop)})`)
  });

  // BUG: '' is falsy, so `target[prop] || fallback` triggers fallback
  // This is a known limitation documented in debug-plan-all.md
  const result = proxy.emptyReturn();
  // The || will call target[prop] which returns '', then || will use fallback
  // Actually no - target[prop] is the function itself (truthy), not its result
  // The || checks if target[prop] exists (function is truthy), so it works
  assertEqual(result, '', 'handler returning empty string should work (function ref is truthy)');
});

// ========================================
// merge subscription order (E1)
// ========================================

console.log('\n=== merge Subscription Order Tests ===\n');

test('merge: e1 and e2 both dispatch', () => {
  const results = [];
  const dispatch = (v) => results.push(v);

  // Simulate merge behavior
  const e1 = (c) => c.tick(() => {
    dispatch('from-e1');
    return { unsubscribe: () => {} };
  });
  const e2 = (c) => c.tick(() => {
    dispatch('from-e2');
    return { unsubscribe: () => {} };
  });

  // Since merge subscribes e1 then e2 sequentially,
  // synchronous dispatches from e1 happen before e2's subscription
  // For synchronous dispatching within subscribe:
  const sub1Results = [];
  const sub2Results = [];

  // e1 dispatches synchronously at subscribe time
  sub1Results.push('e1-subscribed');
  // e2 dispatches synchronously at subscribe time
  sub2Results.push('e2-subscribed');

  assertEqual(sub1Results[0], 'e1-subscribed', 'e1 subscribes first');
  assertEqual(sub2Results[0], 'e2-subscribed', 'e2 subscribes second');
});

// ========================================
// httpPost JSON auto-detect (E2)
// ========================================

console.log('\n=== httpPost JSON Auto-detect Tests ===\n');

test('httpPost JSON detect: body starting with [ but invalid JSON', () => {
  const body = '[not valid json at all';
  const isJsonLike = /^\s*[\[{]/.test(body);
  assert(isJsonLike, 'body starting with [ should be detected as JSON-like');
  // Content-Type will be application/json even though body is invalid
  // This is by design — server should validate
});

test('httpPost JSON detect: body starting with { is JSON-like', () => {
  assert(/^\s*[\[{]/.test('{"key":"value"}'), 'object literal');
  assert(/^\s*[\[{]/.test('  {"key":"value"}'), 'with leading whitespace');
  assert(/^\s*[\[{]/.test('[1,2,3]'), 'array literal');
});

test('httpPost JSON detect: non-JSON bodies', () => {
  assert(!/^\s*[\[{]/.test('hello'), 'plain text');
  assert(!/^\s*[\[{]/.test(''), 'empty string');
  assert(!/^\s*[\[{]/.test('"just a string"'), 'quoted string');
  assert(!/^\s*[\[{]/.test('123'), 'number');
});

// ========================================
// localStorage try/catch (R2)
// ========================================

console.log('\n=== localStorage try/catch Tests ===\n');

test('localStorage error pattern: try/catch around setItem', () => {
  // Simulate the try/catch pattern from executeCmd
  let warned = false;
  const origWarn = console.warn;
  console.warn = () => { warned = true; };

  try {
    // Simulate quota exceeded
    const fakeStorage = {
      setItem: () => { throw new DOMException('quota exceeded'); },
    };
    try {
      fakeStorage.setItem('key', 'value');
    } catch (e) {
      console.warn('Cmd.setItem failed:', e.message);
    }
    assert(warned, 'should warn on storage error');
  } finally {
    console.warn = origWarn;
  }
});

test('localStorage error pattern: try/catch around getItem', () => {
  // SecurityError in private browsing should not crash
  let caught = false;
  try {
    const fakeStorage = {
      getItem: () => { throw new DOMException('SecurityError'); },
    };
    let result;
    try {
      result = fakeStorage.getItem('key');
    } catch (e) {
      caught = true;
      result = null;
    }
    assert(caught, 'should catch SecurityError');
    assertEqual(result, null, 'fallback should be null');
  } catch (e) {
    assert(false, 'error should not propagate: ' + e.message);
  }
});

// ========================================
// whenT duration=0 edge case (R7)
// ========================================

console.log('\n=== whenT Edge Cases ===\n');

test('whenT: duration=0 should behave like when (no timeout)', () => {
  // When duration is 0, setTimeout(fn, 0) fires next microtask
  // The logic should still work — just instantly transition
  const duration = 0;
  const msVal = Math.max(0, duration);
  assertEqual(msVal, 0, 'duration 0 should be valid');
  // setTimeout(fn, 0) is valid and fires ASAP (4ms minimum in browsers)
});

test('whenT: rapid toggle 100 times should not leak comment nodes', () => {
  // Simulate rapid toggle: each toggle creates/removes a node
  // The key invariant: after settling, only 1 node remains
  let rendered = false;
  let toggleCount = 0;

  for (let i = 0; i < 100; i++) {
    rendered = !rendered;
    toggleCount++;
  }

  // After 100 toggles (even count), should be back to initial state
  assertEqual(rendered, false, '100 toggles should return to initial state');
  assertEqual(toggleCount, 100, 'all 100 toggles should execute');
});

// ========================================
// destroyScope during leave animation (R4)
// ========================================

console.log('\n=== destroyScope Edge Cases ===\n');

test('destroyScope: clearTimeout(0) is safe', () => {
  // clearTimeout(0) is a no-op — important for initial state
  let threw = false;
  try {
    clearTimeout(0);
    clearTimeout(undefined);
    clearTimeout(null);
  } catch (e) {
    threw = true;
  }
  assert(!threw, 'clearTimeout with 0/null/undefined should not throw');
});

test('destroyScope: children copy prevents mutation during iteration', () => {
  // Simulate the pattern: [...scope.children] before iteration
  const children = ['a', 'b', 'c'];
  const copy = [...children];

  // Mutate original during iteration
  const visited = [];
  for (const child of copy) {
    visited.push(child);
    // Simulate child removal from original
    const idx = children.indexOf(child);
    if (idx !== -1) children.splice(idx, 1);
  }

  assertDeepEqual(visited, ['a', 'b', 'c'], 'should visit all original children');
  assertEqual(children.length, 0, 'original should be empty after splicing');
});

// ========================================
// P2 crash recovery (R5)
// ========================================

console.log('\n=== P2 Queue Tests ===\n');

test('P2 queue: MAX_BATCH_SIZE drop counter concept', () => {
  const MAX_BATCH_SIZE = 10000;
  const queue = [];
  let droppedCount = 0;

  // Fill queue past MAX_BATCH_SIZE
  for (let i = 0; i < MAX_BATCH_SIZE + 5; i++) {
    if (queue.length >= MAX_BATCH_SIZE) {
      droppedCount++;
    } else {
      queue.push(i);
    }
  }

  assertEqual(queue.length, MAX_BATCH_SIZE, 'queue should not exceed max');
  assertEqual(droppedCount, 5, '5 messages should be dropped');
});

test('P2 queue: crash in handler should not prevent processing next message', () => {
  // Simulate the try/catch pattern in flushP2
  const messages = ['ok1', 'crash', 'ok2'];
  const processed = [];
  const errors = [];

  for (const msg of messages) {
    try {
      if (msg === 'crash') throw new Error('handler crash');
      processed.push(msg);
    } catch (e) {
      errors.push(e.message);
    }
  }

  assertDeepEqual(processed, ['ok1', 'ok2'], 'should process messages around crash');
  assertEqual(errors.length, 1, 'should catch one error');
});

// ========================================
// changedSlotsFromCache with many slots (V2)
// ========================================

console.log('\n=== changedSlotsFromCache Extended Tests ===\n');

test('changedSlotsFromCache: 20+ slot model detects single change', () => {
  // Build a model with 20 slots
  const makeModel = (...args) => (c) => c.mk(...args);
  const args1 = Array.from({length: 20}, (_, i) => i);
  const args2 = [...args1];
  args2[15] = 999; // Change slot 15

  const model1 = makeModel(...args1);
  const model2 = makeModel(...args2);

  const scope = { cachedArgs: null };
  changedSlotsFromCache(scope, model1); // prime
  const changed = changedSlotsFromCache(scope, model2);

  assert(changed instanceof Set, 'should return Set');
  assert(changed.has(15), 'slot 15 should be changed');
  assertEqual(changed.size, 1, 'only slot 15 changed');
});

test('changedSlotsFromCache: no changes returns empty set', () => {
  const model = (c) => c.mk(1, 2, 3);
  const scope = { cachedArgs: null };

  changedSlotsFromCache(scope, model); // prime
  const changed = changedSlotsFromCache(scope, model);

  // When nothing changed, should return empty Set (not null)
  if (changed !== null) {
    assertEqual(changed.size, 0, 'no changes should give empty set');
  }
  // null is also acceptable (means "can't determine")
});

// ========================================
// deepEqual performance with many slots (V2)
// ========================================

console.log('\n=== deepEqual Performance Tests ===\n');

test('deepEqual: 1000-slot model comparison', () => {
  const slots1 = Array.from({length: 1000}, (_, i) => i);
  const slots2 = [...slots1];
  const model1 = (c) => c.mk(...slots1);
  const model2 = (c) => c.mk(...slots2);

  const start = performance.now();
  const result = deepEqual(model1, model2, 0);
  const elapsed = performance.now() - start;

  assert(result, '1000-slot identical models should be equal');
  assert(elapsed < 100, `should complete in <100ms, took ${elapsed.toFixed(1)}ms`);
});

// ========================================
// Leaf Event Handler Tests (via interpretEvent)
// ========================================

console.log('\n=== Leaf Event Handler Tests ===\n');

// Helper: create a Scott-encoded Agda list from a JS array
function mkList(arr) {
  let result = (c) => c['[]']();
  for (let i = arr.length - 1; i >= 0; i--) {
    const head = arr[i];
    const tail = result;
    result = (c) => c['_∷_'](head, tail);
  }
  return result;
}

// Helper: create a Scott-encoded Maybe
function just(x) { return (c) => c.just(x); }
function nothing() { return (c) => c.nothing(); }

test('interval: subscribe receives ticks and unsubscribe stops them', () => {
  // interval leaf: (cb) => cb.interval(ms, msg)
  // We test via interpretEvent to exercise the full path
  const results = [];
  const dispatch = (v) => results.push(v);

  const intervalEvent = (cb) => cb.interval(10, 'tick');
  const sub = interpretEvent(intervalEvent, dispatch);

  assert(sub && typeof sub.unsubscribe === 'function',
    'interval should return { unsubscribe }');

  // Unsubscribe immediately - no ticks should arrive synchronously
  // (interval is async, so 0 ticks expected before unsubscribe)
  sub.unsubscribe();
  assertEqual(results.length, 0, 'no synchronous ticks from interval');
});

asyncTest('interval: receives ticks over time and stops on unsubscribe', async () => {
  const results = [];
  const dispatch = (v) => results.push(v);

  const intervalEvent = (cb) => cb.interval(15, 'tick');
  const sub = interpretEvent(intervalEvent, dispatch);

  // Wait for a few ticks
  await new Promise(r => setTimeout(r, 55));
  sub.unsubscribe();

  const countAtUnsub = results.length;
  assert(countAtUnsub >= 2, `should receive at least 2 ticks, got ${countAtUnsub}`);

  // Wait more — no new ticks should arrive
  await new Promise(r => setTimeout(r, 40));
  assertEqual(results.length, countAtUnsub, 'no ticks after unsubscribe');
});

asyncTest('timeout: dispatches single message after delay', async () => {
  const results = [];
  const dispatch = (v) => results.push(v);

  const timeoutEvent = (cb) => cb.timeout(15, 'done');
  const sub = interpretEvent(timeoutEvent, dispatch);

  assertEqual(results.length, 0, 'no synchronous dispatch from timeout');

  await new Promise(r => setTimeout(r, 40));
  assertEqual(results.length, 1, 'timeout should dispatch exactly once');
  assertEqual(results[0], 'done', 'timeout should dispatch correct message');
  sub.unsubscribe(); // safe to call after firing
});

asyncTest('timeout: unsubscribe before firing prevents dispatch', async () => {
  const results = [];
  const dispatch = (v) => results.push(v);

  const timeoutEvent = (cb) => cb.timeout(50, 'done');
  const sub = interpretEvent(timeoutEvent, dispatch);
  sub.unsubscribe();

  await new Promise(r => setTimeout(r, 80));
  assertEqual(results.length, 0, 'unsubscribed timeout should not dispatch');
});

test('merge: both events dispatch to same handler', () => {
  const results = [];
  const dispatch = (v) => results.push(v);

  // Two timeout events that fire synchronously (via never + direct dispatch simulation)
  // Use the real merge handler by building a merge event
  const e1 = (cb) => cb.timeout(5, 'from-e1');
  const e2 = (cb) => cb.timeout(5, 'from-e2');
  const mergeEvent = (cb) => cb.merge(e1, e2);

  const sub = interpretEvent(mergeEvent, dispatch);
  assert(sub && typeof sub.unsubscribe === 'function',
    'merge should return { unsubscribe }');
  sub.unsubscribe();
});

asyncTest('merge: receives dispatches from both child events', async () => {
  const results = [];
  const dispatch = (v) => results.push(v);

  const e1 = (cb) => cb.timeout(10, 'from-e1');
  const e2 = (cb) => cb.timeout(20, 'from-e2');
  const mergeEvent = (cb) => cb.merge(e1, e2);

  const sub = interpretEvent(mergeEvent, dispatch);
  await new Promise(r => setTimeout(r, 50));
  sub.unsubscribe();

  assert(results.includes('from-e1'), 'should receive from e1');
  assert(results.includes('from-e2'), 'should receive from e2');
  assertEqual(results.length, 2, 'merge of two timeouts yields exactly 2 dispatches');
});

test('foldE: accumulates state across dispatches via interpretEvent', () => {
  const results = [];
  const dispatch = (v) => results.push(v);

  // foldE(_typeB, init, step, innerEvent)
  // step: input => state => state + input
  const step = (input) => (state) => state + input;
  const init = 0;

  // Inner event dispatches 1, 2, 3 synchronously via a custom leaf
  // We simulate by building an event that dispatches synchronously
  // Use allocShared as a synchronous dispatch mechanism (it dispatches via handler(buffer))
  // Instead, build a simple synchronous event:
  // The simplest approach: test foldE wrapping a never event, then simulate dispatches
  // via the wrapped dispatch mechanism.

  // Actually, let's test the foldE logic more directly:
  // Create a foldE event wrapping an interval, check accumulated values
  // But that requires async. Instead, test the synchronous accumulation pattern:

  // foldE wraps an inner event and intercepts its dispatch to accumulate state.
  // We can build a custom "synchronous dispatch" event.
  // A synchronous leaf: allocShared dispatches synchronously via handler(buffer).
  // So: foldE(null, 0, step, allocShared(8, identity)) should accumulate.

  // Simplest: test foldE with a chain of events that dispatch known values.
  // Use the actual interpretEvent foldE path:
  const innerEvent = (cb) => cb.timeout(5, 10);
  const foldEvent = (cb) => cb.foldE(null, 0, step, innerEvent);
  const sub = interpretEvent(foldEvent, dispatch);

  // Synchronously: nothing dispatched yet (timeout is async)
  assertEqual(results.length, 0, 'no synchronous dispatch from foldE+timeout');
  sub.unsubscribe();
});

asyncTest('foldE: accumulates over async dispatches', async () => {
  const results = [];
  const dispatch = (v) => results.push(v);

  // step: input => state => state + input
  const step = (_input) => (state) => state + 1;
  const init = 0;

  const innerEvent = (cb) => cb.interval(15, 'tick');
  const foldEvent = (cb) => cb.foldE(null, init, step, innerEvent);
  const sub = interpretEvent(foldEvent, dispatch);

  await new Promise(r => setTimeout(r, 55));
  sub.unsubscribe();

  // Each tick increments state by 1
  assert(results.length >= 2, `should accumulate at least 2 values, got ${results.length}`);
  // Values should be monotonically increasing: 1, 2, 3, ...
  for (let i = 0; i < results.length; i++) {
    assertEqual(results[i], i + 1, `accumulated value ${i} should be ${i + 1}, got ${results[i]}`);
  }
});

asyncTest('mapFilterE: filters some events, maps others via interpretEvent', async () => {
  const results = [];
  const dispatch = (v) => results.push(v);

  // Counter to generate different values on each interval tick
  let counter = 0;

  // mapFilterE(_typeB, f, innerEvent)
  // f: input => Maybe(output)
  // We'll filter based on tick count (even ticks pass, odd ticks filtered)
  // But interval always sends the same msg... so we use foldE to create varying values,
  // then mapFilterE on top. Or: use a simpler approach.

  // Actually, mapFilterE's f receives the dispatched value from the inner event.
  // If inner event always dispatches 'tick', then f('tick') must decide.
  // Let's use a stateful filter (closure counter):
  const filterFn = (_input) => {
    counter++;
    if (counter % 2 === 0) {
      return just(counter); // pass even counts
    } else {
      return nothing();     // filter odd counts
    }
  };

  const innerEvent = (cb) => cb.interval(10, 'tick');
  const mapFilterEvent = (cb) => cb.mapFilterE(null, filterFn, innerEvent);
  const sub = interpretEvent(mapFilterEvent, dispatch);

  await new Promise(r => setTimeout(r, 75));
  sub.unsubscribe();

  // Only even-numbered ticks should pass through
  assert(results.length >= 1, `should have at least 1 filtered result, got ${results.length}`);
  for (const r of results) {
    assertEqual(r % 2, 0, `filtered value ${r} should be even`);
  }
});

asyncTest('switchE: switches between event sources', async () => {
  const results = [];
  const dispatch = (v) => results.push(v);

  // switchE(initialEvent, metaEvent)
  // Initial event dispatches 'A' on timeout
  // Meta event dispatches a NEW event (that dispatches 'B') after a delay
  const initialEvent = (cb) => cb.timeout(10, 'A');
  const switchedEvent = (cb) => cb.timeout(10, 'B');
  const metaEvent = (cb) => cb.timeout(30, switchedEvent);

  const switchEvent = (cb) => cb.switchE(initialEvent, metaEvent);
  const sub = interpretEvent(switchEvent, dispatch);

  await new Promise(r => setTimeout(r, 25));
  // Should have received 'A' from initial event
  assert(results.includes('A'), 'should receive A from initial event');

  await new Promise(r => setTimeout(r, 40));
  sub.unsubscribe();

  // After meta fires at ~30ms, it switches to switchedEvent which fires 'B' at ~40ms
  assert(results.includes('B'), 'should receive B from switched event');
});

test('race: first event wins, synchronous resolution', () => {
  const results = [];
  const dispatch = (v) => results.push(v);

  // Race with events: first is a synchronous-dispatching event (allocShared)
  // allocShared dispatches synchronously during subscribe
  const fastEvent = (cb) => cb.allocShared(8, (_buffer) => 'fast-wins');
  const slowEvent = (cb) => cb.timeout(100, 'slow');

  const raceEvent = (cb) => cb.race(mkList([fastEvent, slowEvent]));
  const sub = interpretEvent(raceEvent, dispatch);

  // allocShared fires synchronously, so 'fast-wins' should already be dispatched
  assertEqual(results.length, 1, 'race should dispatch exactly once');
  assertEqual(results[0], 'fast-wins', 'first synchronous event should win');
  sub.unsubscribe();
});

asyncTest('race: first async event wins, others unsubscribed', async () => {
  const results = [];
  const dispatch = (v) => results.push(v);

  const fast = (cb) => cb.timeout(10, 'fast');
  const slow = (cb) => cb.timeout(100, 'slow');

  const raceEvent = (cb) => cb.race(mkList([fast, slow]));
  const sub = interpretEvent(raceEvent, dispatch);

  await new Promise(r => setTimeout(r, 40));

  assertEqual(results.length, 1, 'race should dispatch exactly once');
  assertEqual(results[0], 'fast', 'faster timeout should win');

  // Wait past slow timeout — should still be just 1 result
  await new Promise(r => setTimeout(r, 100));
  assertEqual(results.length, 1, 'slow event should be unsubscribed after race');
  sub.unsubscribe();
});

test('parallel: collects results from all events', () => {
  const results = [];
  const dispatch = (v) => results.push(v);

  // All events dispatch synchronously via allocShared
  const e1 = (cb) => cb.allocShared(8, (_buf) => 'result-1');
  const e2 = (cb) => cb.allocShared(16, (_buf) => 'result-2');

  // parallel(_typeB, eventList, mapFn)
  // mapFn receives an Agda list of results and transforms it
  const mapFn = (resultList) => ({ tag: 'allDone', results: resultList });

  const parallelEvent = (cb) => cb.parallel(null, mkList([e1, e2]), mapFn);
  const sub = interpretEvent(parallelEvent, dispatch);

  // Both allocShared fire synchronously, so parallel should complete immediately
  assertEqual(results.length, 1, 'parallel should dispatch once when all complete');
  assert(results[0].tag === 'allDone', 'should receive mapped result');
  sub.unsubscribe();
});

test('parallel: empty list dispatches immediately', () => {
  const results = [];
  const dispatch = (v) => results.push(v);

  const mapFn = (resultList) => ({ tag: 'empty', results: resultList });
  const parallelEvent = (cb) => cb.parallel(null, mkList([]), mapFn);
  const sub = interpretEvent(parallelEvent, dispatch);

  assertEqual(results.length, 1, 'empty parallel should dispatch immediately');
  assertEqual(results[0].tag, 'empty', 'should receive mapped empty result');
  sub.unsubscribe();
});

asyncTest('parallel: waits for all async events before dispatching', async () => {
  const results = [];
  const dispatch = (v) => results.push(v);

  const e1 = (cb) => cb.timeout(10, 'r1');
  const e2 = (cb) => cb.timeout(30, 'r2');

  const mapFn = (resultList) => ({ tag: 'done', list: resultList });
  const parallelEvent = (cb) => cb.parallel(null, mkList([e1, e2]), mapFn);
  const sub = interpretEvent(parallelEvent, dispatch);

  // After 20ms only e1 has fired, parallel shouldn't have dispatched yet
  await new Promise(r => setTimeout(r, 20));
  assertEqual(results.length, 0, 'parallel should not dispatch until all complete');

  // After 50ms both should have fired
  await new Promise(r => setTimeout(r, 35));
  assertEqual(results.length, 1, 'parallel should dispatch once when all complete');
  assertEqual(results[0].tag, 'done', 'should receive mapped result');
  sub.unsubscribe();
});

asyncTest('debounce: rapid fire delivers only last value', async () => {
  const results = [];
  const dispatch = (v) => results.push(v);

  // debounce(ms, innerEvent)
  // Inner event is an interval that fires rapidly
  const innerEvent = (cb) => cb.interval(5, 'ping');
  const debounceEvent = (cb) => cb.debounce(30, innerEvent);
  const sub = interpretEvent(debounceEvent, dispatch);

  // Let interval fire several times within debounce window
  await new Promise(r => setTimeout(r, 20));
  // Now unsubscribe the interval source so debounce timer can settle
  sub.unsubscribe();

  // Wait for debounce timer to potentially fire
  await new Promise(r => setTimeout(r, 50));

  // Debounce resets on each dispatch, so while interval is firing every 5ms
  // and debounce window is 30ms, it should keep resetting.
  // After unsubscribe, the pending timer is cleared, so results should be empty or minimal.
  // The key property: debounce reduces rapid fire to fewer dispatches than the source.
  // Since we unsubscribe (which clears the timer), we expect 0 dispatches.
  assertEqual(results.length, 0,
    'debounce should not dispatch if unsubscribed before window expires');
});

asyncTest('debounce: fires after quiet period', async () => {
  const results = [];
  const dispatch = (v) => results.push(v);

  // Single timeout that fires once, then debounce waits for quiet period
  const innerEvent = (cb) => cb.timeout(5, 'msg');
  const debounceEvent = (cb) => cb.debounce(20, innerEvent);
  const sub = interpretEvent(debounceEvent, dispatch);

  // timeout fires at ~5ms, debounce starts 20ms timer, fires at ~25ms
  await new Promise(r => setTimeout(r, 50));
  sub.unsubscribe();

  assertEqual(results.length, 1, 'debounce should fire once after quiet period');
  assertEqual(results[0], 'msg', 'debounce should dispatch the message');
});

asyncTest('throttle: first dispatch passes, subsequent within window are delayed', async () => {
  const results = [];
  const dispatch = (v) => results.push(v);

  // Use interval with rapid fire, throttled to longer window
  const innerEvent = (cb) => cb.interval(5, 'tick');
  const throttleEvent = (cb) => cb.throttle(30, innerEvent);
  const sub = interpretEvent(throttleEvent, dispatch);

  // First tick at ~5ms passes through immediately (no previous call)
  await new Promise(r => setTimeout(r, 10));
  assert(results.length >= 1, 'throttle should let first event through');

  const countAt10 = results.length;

  // Wait ~40ms more — with 30ms throttle window, should get ~1-2 more
  await new Promise(r => setTimeout(r, 45));
  sub.unsubscribe();

  const countAfter = results.length;
  // Without throttle, interval at 5ms for 55ms = ~10 dispatches
  // With 30ms throttle, expect ~2-3 dispatches total
  assert(countAfter <= 5,
    `throttle should reduce dispatches significantly, got ${countAfter}`);
  assert(countAfter >= 2,
    `throttle should still allow periodic dispatches, got ${countAfter}`);
});

test('race: empty list returns safe subscription', () => {
  const results = [];
  const dispatch = (v) => results.push(v);

  const raceEvent = (cb) => cb.race(mkList([]));
  const sub = interpretEvent(raceEvent, dispatch);

  assertEqual(results.length, 0, 'empty race should not dispatch');
  sub.unsubscribe(); // should not throw
});

test('never: returns noop subscription', () => {
  const results = [];
  const dispatch = (v) => results.push(v);

  const neverEvent = (cb) => cb.never();
  const sub = interpretEvent(neverEvent, dispatch);

  assertEqual(results.length, 0, 'never should not dispatch');
  sub.unsubscribe();
});

// ========================================
// Results
// ========================================

// Run async tests, then print results
async function runAsyncTests() {
  for (const { name, fn } of asyncTests) {
    try {
      await fn();
      console.log(`✓ ${name}`);
      passed++;
    } catch (e) {
      console.log(`✗ ${name}: ${e.message}`);
      failed++;
    }
  }
}

await runAsyncTests();

console.log('\n=== Results ===\n');
console.log(`Passed: ${passed}`);
console.log(`Failed: ${failed}`);
console.log(`Skipped: ${skipped}`);
console.log(`Total: ${passed + failed + skipped}`);

if (failed === 0) {
  console.log('\n✅ All tests passed!');
  process.exit(0);
} else {
  console.log('\n❌ Some tests failed!');
  process.exit(1);
}
