/**
 * Agdelte Data.Array FFI Tests
 */

import ArrayModule from '../_build/jAgda.Agdelte.Data.Array.mjs';

const { index, find, findIndex, elem, toList, fromList,
        length: arrayLength, map: arrayMap,
        filter: arrayFilter, foldl, foldr } = ArrayModule;
const arrayNull = ArrayModule["null"];

// Simple test runner
let passed = 0;
let failed = 0;

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

// Scott-encoding helpers
const matchBool = (b) => b({"true": () => true, "false": () => false});
const matchMaybe = (m) => m({just: x => x, nothing: () => null});

function collectList(list) {
  const arr = [];
  let cur = list;
  let done = false;
  while (!done) {
    cur({ '[]': () => { done = true; },
          '_∷_': (head, tail) => { arr.push(head); cur = tail; }});
  }
  return arr;
}

// Scott Bool predicates (Array FFI expects predicates returning Scott Bool)
const pred20 = (x) => x === 20
  ? (cases) => cases["true"]()
  : (cases) => cases["false"]();

const predNever = (_) => (cases) => cases["false"]();

const eqNum = (a) => (b) => a === b
  ? (cases) => cases["true"]()
  : (cases) => cases["false"]();

// ========================================
// Tests
// ========================================

console.log('\n=== Data.Array FFI Tests ===\n');

test('index: valid index returns element', () => {
  assertEqual(matchMaybe(index(0n)([10, 20, 30])), 10);
});

test('index: out of bounds returns nothing', () => {
  assertEqual(matchMaybe(index(5n)([10])), null);
});

test('find: existing element', () => {
  assertEqual(matchMaybe(find(pred20)([10, 20, 30])), 20);
});

test('find: no match returns nothing', () => {
  assertEqual(matchMaybe(find(predNever)([10, 20, 30])), null);
});

test('findIndex: existing element', () => {
  assertEqual(matchMaybe(findIndex(pred20)([10, 20, 30])), 1n);
});

test('findIndex: no match returns nothing', () => {
  assertEqual(matchMaybe(findIndex(predNever)([10, 20, 30])), null);
});

test('elem: element present', () => {
  assertEqual(matchBool(elem(eqNum)(20)([10, 20, 30])), true);
});

test('elem: element absent', () => {
  assertEqual(matchBool(elem(eqNum)(99)([10, 20, 30])), false);
});

test('toList: converts array to linked list', () => {
  assertDeepEqual(collectList(toList([1, 2, 3])), [1, 2, 3]);
});

test('toList: empty array', () => {
  assertDeepEqual(collectList(toList([])), []);
});

test('length: returns BigInt length', () => {
  assertEqual(arrayLength([1, 2, 3]), 3n);
});

test('length: empty array', () => {
  assertEqual(arrayLength([]), 0n);
});

test('null: empty array is null', () => {
  assertEqual(matchBool(arrayNull([])), true);
});

test('null: non-empty array is not null', () => {
  assertEqual(matchBool(arrayNull([1])), false);
});

test('map: applies function', () => {
  assertDeepEqual(arrayMap(x => x * 2)([1, 2, 3]), [2, 4, 6]);
});

test('filter: keeps matching elements', () => {
  const gt2 = (x) => x > 2
    ? (cases) => cases["true"]()
    : (cases) => cases["false"]();
  assertDeepEqual(arrayFilter(gt2)([1, 2, 3, 4]), [3, 4]);
});

test('foldl: left fold', () => {
  assertEqual(foldl(acc => x => acc + x)(0)([1, 2, 3]), 6);
});

test('foldr: right fold', () => {
  assertEqual(foldr(x => acc => x - acc)(0)([1, 2, 3]), 2);
});

console.log(`\nPassed: ${passed}, Failed: ${failed}, Total: ${passed + failed}`);
process.exit(failed > 0 ? 1 : 0);
