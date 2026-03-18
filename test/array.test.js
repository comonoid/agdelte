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

// ========================================
// Additional Array Tests (A53, T4)
// ========================================

import ArrayModuleFull from '../_build/jAgda.Agdelte.Data.Array.mjs';
const { sortBy, take, drop, reverse, slice, singleton, empty, replicate, snoc, cons: arrayCons, append } = ArrayModuleFull;

console.log('\n=== Array Extended Tests ===\n');

// Sort comparator for numbers
const numCmp = (a) => (b) => {
  if (a < b) return (c) => c.lt();
  if (a > b) return (c) => c.gt();
  return (c) => c.eq();
};

test('sortBy: sorts numbers ascending', () => {
  assertDeepEqual(sortBy(numCmp)([3, 1, 4, 1, 5, 9]), [1, 1, 3, 4, 5, 9]);
});

test('sortBy: stability (equal elements keep order)', () => {
  const items = [{v: 2, id: 'a'}, {v: 1, id: 'b'}, {v: 2, id: 'c'}, {v: 1, id: 'd'}];
  const cmp = (a) => (b) => {
    if (a.v < b.v) return (c) => c.lt();
    if (a.v > b.v) return (c) => c.gt();
    return (c) => c.eq();
  };
  const sorted = sortBy(cmp)(items);
  assertEqual(sorted[0].id, 'b', 'first 1 should be b');
  assertEqual(sorted[1].id, 'd', 'second 1 should be d');
  assertEqual(sorted[2].id, 'a', 'first 2 should be a');
  assertEqual(sorted[3].id, 'c', 'second 2 should be c');
});

test('sortBy: empty array', () => {
  assertDeepEqual(sortBy(numCmp)([]), []);
});

test('sortBy: single element', () => {
  assertDeepEqual(sortBy(numCmp)([42]), [42]);
});

test('take: first N elements', () => {
  assertDeepEqual(take(3n)([1, 2, 3, 4, 5]), [1, 2, 3]);
});

test('take: N > length returns all', () => {
  assertDeepEqual(take(10n)([1, 2]), [1, 2]);
});

test('take: 0 returns empty', () => {
  assertDeepEqual(take(0n)([1, 2, 3]), []);
});

test('drop: remove first N', () => {
  assertDeepEqual(drop(2n)([1, 2, 3, 4]), [3, 4]);
});

test('drop: N > length returns empty', () => {
  assertDeepEqual(drop(10n)([1, 2]), []);
});

test('reverse: reverses array', () => {
  assertDeepEqual(reverse([1, 2, 3]), [3, 2, 1]);
});

test('reverse: does not mutate original', () => {
  const orig = [1, 2, 3];
  reverse(orig);
  assertDeepEqual(orig, [1, 2, 3], 'original should be unchanged');
});

test('reverse: empty', () => {
  assertDeepEqual(reverse([]), []);
});

test('slice: range', () => {
  assertDeepEqual(slice(1n)(3n)([10, 20, 30, 40, 50]), [20, 30]);
});

test('singleton: creates 1-element array', () => {
  assertDeepEqual(singleton(42), [42]);
});

test('empty: creates empty array', () => {
  assertDeepEqual(empty, []);
});

test('replicate: creates N copies', () => {
  assertDeepEqual(replicate(3n)('x'), ['x', 'x', 'x']);
});

test('snoc: append to end', () => {
  assertDeepEqual(snoc([1, 2])(3), [1, 2, 3]);
});

test('cons: prepend to front', () => {
  assertDeepEqual(arrayCons(0)([1, 2]), [0, 1, 2]);
});

test('append: concatenate', () => {
  assertDeepEqual(append([1, 2])([3, 4]), [1, 2, 3, 4]);
});

test('fromList -> toList roundtrip', () => {
  const arr = [10, 20, 30];
  const list = toList(arr);
  const back = ArrayModuleFull.fromList(list);
  assertDeepEqual(back, arr, 'roundtrip should preserve elements');
});

test('index: negative index returns just(undefined) due to idx < length check', () => {
  // BigInt(-1) → Number(-1) → -1 < 3 → just(arr[-1]) → just(undefined)
  // This is a known edge case: no guard for negative indices
  const result = matchMaybe(index(-1n)([10, 20, 30]));
  assertEqual(result, undefined, 'negative index returns just(undefined)');
});

console.log(`\nPassed: ${passed}, Failed: ${failed}, Total: ${passed + failed}`);
process.exit(failed > 0 ? 1 : 0);
