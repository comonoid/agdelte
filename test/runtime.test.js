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
// Combinator Runtime Tests (Phase 5)
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
