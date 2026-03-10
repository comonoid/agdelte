/**
 * Agdelte Json Encoder/Decoder FFI Tests
 */

import JsonModule from '../_build/jAgda.Agdelte.Json.mjs';

const { encodeBool, encodeInt, encodeNat, encodeString, encodeFloat,
        encodeList, encodeMaybe, encodeArray,
        decodeString: decodeStringFn,
        string: stringDecoder, bool: boolDecoder, nat: natDecoder,
        map2 } = JsonModule;
const fieldDecoder = JsonModule["field′"];

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

// Scott constructors for test inputs
const scottTrue  = (cases) => cases["true"]();
const scottFalse = (cases) => cases["false"]();
const scottJust    = (x) => (cases) => cases.just(x);
const scottNothing = (cases) => cases.nothing();
const scottNil = (cases) => cases['[]']();
const scottCons = (h, t) => (cases) => cases['_∷_'](h, t);
const scottPosInt = (n) => (cases) => cases["+_"](n);
const scottNegInt = (n) => (cases) => cases["-[1+_]"](n);

// Scott Result helper
const matchResult = (r) => r({ok: v => ({tag: 'ok', value: v}), err: e => ({tag: 'err', error: e})});

// ========================================
// Encoder Tests
// ========================================

console.log('\n=== Json Encoder Tests ===\n');

test('encodeBool: true', () => {
  assertEqual(encodeBool.encode(scottTrue), true);
});

test('encodeBool: false', () => {
  assertEqual(encodeBool.encode(scottFalse), false);
});

test('encodeInt: positive', () => {
  assertEqual(encodeInt.encode(scottPosInt(42n)), 42);
});

test('encodeInt: negative (-3 = -[1+ 2])', () => {
  assertEqual(encodeInt.encode(scottNegInt(2n)), -3);
});

test('encodeNat: 5', () => {
  assertEqual(encodeNat.encode(5n), 5);
});

test('encodeString: hello', () => {
  assertEqual(encodeString.encode("hello"), "hello");
});

test('encodeList(encodeString): empty', () => {
  assertDeepEqual(encodeList(encodeString).encode(scottNil), []);
});

test('encodeList(encodeString): ["a", "b"]', () => {
  const list = scottCons("a", scottCons("b", scottNil));
  assertDeepEqual(encodeList(encodeString).encode(list), ["a", "b"]);
});

test('encodeMaybe(encodeString): just "x"', () => {
  assertEqual(encodeMaybe(encodeString).encode(scottJust("x")), "x");
});

test('encodeMaybe(encodeString): nothing', () => {
  assertEqual(encodeMaybe(encodeString).encode(scottNothing), null);
});

// ========================================
// Decoder Tests
// ========================================

console.log('\n=== Json Decoder Tests ===\n');

test('stringDecoder: valid string', () => {
  const result = stringDecoder.decode("hello");
  assertEqual(result.tag, 'ok');
  assertEqual(result.value, "hello");
});

test('stringDecoder: invalid (number)', () => {
  const result = stringDecoder.decode(42);
  assertEqual(result.tag, 'err');
});

test('boolDecoder: true', () => {
  const result = boolDecoder.decode(true);
  assertEqual(result.tag, 'ok');
  assertEqual(matchBool(result.value), true);
});

test('boolDecoder: false', () => {
  const result = boolDecoder.decode(false);
  assertEqual(result.tag, 'ok');
  assertEqual(matchBool(result.value), false);
});

test('natDecoder: valid nat', () => {
  const result = natDecoder.decode(5);
  assertEqual(result.tag, 'ok');
  assertEqual(result.value, 5n);
});

test('natDecoder: negative fails', () => {
  const result = natDecoder.decode(-1);
  assertEqual(result.tag, 'err');
});

// ========================================
// decodeString Tests (parses JSON string)
// ========================================

console.log('\n=== Json decodeString Tests ===\n');

test('decodeString: valid JSON string', () => {
  const result = matchResult(decodeStringFn(stringDecoder)('"hello"'));
  assertEqual(result.tag, 'ok');
  assertEqual(result.value, "hello");
});

test('decodeString: invalid JSON', () => {
  const result = matchResult(decodeStringFn(stringDecoder)('invalid'));
  assertEqual(result.tag, 'err');
  assert(result.error.startsWith('JSON parse error:'), `Expected JSON parse error, got: ${result.error}`);
});

test('decodeString: type mismatch', () => {
  const result = matchResult(decodeStringFn(stringDecoder)('42'));
  assertEqual(result.tag, 'err');
});

// ========================================
// map2 / field Tests
// ========================================

console.log('\n=== Json Combinator Tests ===\n');

test('map2 with field decoders', () => {
  const decoder = map2(a => b => ({name: a, age: Number(b)}))(
    fieldDecoder("name")(stringDecoder)
  )(
    fieldDecoder("age")(natDecoder)
  );
  const result = decoder.decode({name: "Alice", age: 30});
  assertEqual(result.tag, 'ok');
  assertEqual(result.value.name, "Alice");
  assertEqual(result.value.age, 30);
});

console.log(`\nPassed: ${passed}, Failed: ${failed}, Total: ${passed + failed}`);
process.exit(failed > 0 ? 1 : 0);
