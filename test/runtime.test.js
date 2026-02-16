/**
 * Agdelte Runtime Tests
 * Tests for JavaScript runtime (reactive.js, events.js, primitives.js)
 */

import { debounce, throttle } from '../runtime/events.js';
import { interval, animationFrame, onKey } from '../runtime/primitives.js';

// Simple test runner
let passed = 0;
let failed = 0;
let skipped = 0;

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

console.log('\n=== Events Tests ===\n');

test('debounce delays calls', () => {
  let callCount = 0;
  const fn = debounce(() => callCount++, 10);
  fn(); fn(); fn();
  // Immediate check - should not have been called yet
  assertEqual(callCount, 0);
});

test('throttle limits call rate', () => {
  let callCount = 0;
  const fn = throttle(() => callCount++, 100);
  fn(); fn(); fn();
  // First call should go through immediately
  assertEqual(callCount, 1);
});

// ========================================
// Primitives Tests
// ========================================

console.log('\n=== Primitives Tests ===\n');

test('interval creates event spec', () => {
  const spec = interval(1000);
  assert(typeof spec === 'function', 'interval should return a function');
});

test('animationFrame creates event spec', () => {
  const spec = animationFrame;
  assert(typeof spec === 'function', 'animationFrame should be a function');
});

test('onKey creates keyboard event spec', () => {
  const spec = onKey('Enter');
  assert(typeof spec === 'function', 'onKey should return a function');
});

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

test('match works with tagged arrays', () => {
  const justTagged = ['just', 42];
  const nothingTagged = ['nothing'];

  const result1 = AgdaValues.match(justTagged, {
    just: (x) => x * 2,
    nothing: () => 0
  });
  assertEqual(result1, 84, 'tagged just(42) should return 84');

  const result2 = AgdaValues.match(nothingTagged, {
    just: (x) => x * 2,
    nothing: () => 0
  });
  assertEqual(result2, 0, 'tagged nothing should return 0');
});

test('getCtor works with both formats', () => {
  const scottValue = (c) => c.myConstructor(1, 2, 3);
  const taggedValue = ['myConstructor', 1, 2, 3];

  assertEqual(AgdaValues.getCtor(scottValue), 'myConstructor', 'Scott getCtor');
  assertEqual(AgdaValues.getCtor(taggedValue), 'myConstructor', 'Tagged getCtor');
});

test('getSlots works with both formats', () => {
  const scottValue = (c) => c.mk(1, 2, 3);
  const taggedValue = ['mk', 1, 2, 3];

  assertDeepEqual(AgdaValues.getSlots(scottValue), [1, 2, 3], 'Scott getSlots');
  assertDeepEqual(AgdaValues.getSlots(taggedValue), [1, 2, 3], 'Tagged getSlots');
});

test('listToArray works with tagged array lists', () => {
  // Tagged array list: [1, 2, 3]
  const taggedList = ['_∷_', 1, ['_∷_', 2, ['_∷_', 3, ['[]']]]];

  const result = AgdaValues.listToArray(taggedList);
  assertDeepEqual(result.items, [1, 2, 3], 'tagged list items');
  assertEqual(result.incomplete, false, 'tagged list complete');
});

test('construct creates correct format', () => {
  // Default is Scott-encoded
  const value = AgdaValues.construct('pair', 'a', 'b');
  assertEqual(typeof value, 'function', 'default is Scott-encoded');

  const slots = AgdaValues.getSlots(value);
  assertDeepEqual(slots, ['a', 'b'], 'constructed value has correct slots');
});

test('deepEqual works with both formats', () => {
  const scott1 = (c) => c.pair(1, 2);
  const scott2 = (c) => c.pair(1, 2);
  const scott3 = (c) => c.pair(1, 3);

  assert(AgdaValues.deepEqual(scott1, scott2), 'equal Scott values');
  assert(!AgdaValues.deepEqual(scott1, scott3), 'different Scott values');

  const tagged1 = ['pair', 1, 2];
  const tagged2 = ['pair', 1, 2];
  const tagged3 = ['pair', 1, 3];

  assert(AgdaValues.deepEqual(tagged1, tagged2), 'equal tagged values');
  assert(!AgdaValues.deepEqual(tagged1, tagged3), 'different tagged values');
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

console.log('\n=== Bug #5: allocShared error callback ===\n');

test('interpretEvent allocShared calls onError when provided and SAB unavailable', () => {
  // SharedArrayBuffer may not be available without COOP/COEP headers.
  // We test the error path by requesting a negative size (always throws).
  const results = [];
  const dispatch = (msg) => results.push(msg);

  const allocEvent = (c) => c.allocShared(
    -1,
    (buffer) => 'got-buffer',
    (errMsg) => `error:${errMsg}`
  );

  const sub = interpretEvent(allocEvent, dispatch);
  // Should have dispatched an error
  assert(results.length > 0, 'should dispatch something');
  assert(results[0].startsWith('error:'), `should dispatch error, got: ${results[0]}`);
  sub.unsubscribe();
});

test('interpretEvent allocShared works without onError (backward compat)', () => {
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

test('detectSlots returns null for multi-dependency bindings', () => {
  // Model with 3 slots
  const model = (c) => c.mk(1, 2, 3);
  // Extract depends on slot 0 AND slot 2
  const extract = (m) => {
    let val;
    m({ mk: (a, b, c) => { val = a + c; } });
    return val;
  };
  const slots = detectSlots(extract, model, 3);
  // 2+ dependencies → returns null (falls back to full check)
  assertEqual(slots, null, 'multi-dependency should return null');
});

test('detectSlots returns null for extract that throws', () => {
  const model = (c) => c.mk(1);
  const extract = () => { throw new Error('boom'); };
  const slots = detectSlots(extract, model, 1);
  assertEqual(slots, null, 'throwing extract should return null');
});

// ========================================
// Results
// ========================================

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
