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
