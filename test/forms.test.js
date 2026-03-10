/**
 * Agdelte Forms Validator FFI Tests
 */

import FormsModule from '../_build/jAgda.Agdelte.Forms.mjs';

const { email, url, numeric, alphanumeric, equals, notEquals,
        inRange, positive } = FormsModule;
const pattern_ = FormsModule["pattern′"];

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

// Scott-encoding helpers
function collectErrors(list) {
  const errors = [];
  let cur = list;
  let done = false;
  while (!done) {
    cur({ '[]': () => { done = true; },
          '_∷_': (e, tail) => {
            e({ mkError: (field, msg) => errors.push({field, msg}) });
            cur = tail;
          }});
  }
  return errors;
}

// ========================================
// Tests
// ========================================

console.log('\n=== Forms Validator Tests ===\n');

// email
test('email: valid email returns 0 errors', () => {
  const errors = collectErrors(email("a@b.com"));
  assertEqual(errors.length, 0);
});

test('email: invalid email returns 1 error', () => {
  const errors = collectErrors(email("not-email"));
  assertEqual(errors.length, 1);
  assertEqual(errors[0].msg, "Invalid email format");
});

// url
test('url: valid URL returns 0 errors', () => {
  const errors = collectErrors(url("https://example.com"));
  assertEqual(errors.length, 0);
});

test('url: invalid URL returns 1 error', () => {
  const errors = collectErrors(url("not-a-url"));
  assertEqual(errors.length, 1);
});

// numeric
test('numeric: digits return 0 errors', () => {
  const errors = collectErrors(numeric("123"));
  assertEqual(errors.length, 0);
});

test('numeric: non-digits return 1 error', () => {
  const errors = collectErrors(numeric("abc"));
  assertEqual(errors.length, 1);
});

// alphanumeric
test('alphanumeric: valid returns 0 errors', () => {
  const errors = collectErrors(alphanumeric("abc123"));
  assertEqual(errors.length, 0);
});

test('alphanumeric: spaces return 1 error', () => {
  const errors = collectErrors(alphanumeric("a b c"));
  assertEqual(errors.length, 1);
});

// equals
test('equals: matching strings return 0 errors', () => {
  const errors = collectErrors(equals("foo")("foo"));
  assertEqual(errors.length, 0);
});

test('equals: different strings return 1 error', () => {
  const errors = collectErrors(equals("foo")("bar"));
  assertEqual(errors.length, 1);
});

// notEquals
test('notEquals: different strings return 0 errors', () => {
  const errors = collectErrors(notEquals("foo")("bar"));
  assertEqual(errors.length, 0);
});

test('notEquals: same strings return 1 error', () => {
  const errors = collectErrors(notEquals("foo")("foo"));
  assertEqual(errors.length, 1);
});

// inRange
test('inRange: value in range returns 0 errors', () => {
  const errors = collectErrors(inRange(1n)(10n)("5"));
  assertEqual(errors.length, 0);
});

test('inRange: value out of range returns 1 error', () => {
  const errors = collectErrors(inRange(1n)(10n)("15"));
  assertEqual(errors.length, 1);
});

test('inRange: non-numeric returns 1 error', () => {
  const errors = collectErrors(inRange(1n)(10n)("abc"));
  assertEqual(errors.length, 1);
});

// positive
test('positive: positive number returns 0 errors', () => {
  const errors = collectErrors(positive("1"));
  assertEqual(errors.length, 0);
});

test('positive: zero returns 1 error', () => {
  const errors = collectErrors(positive("0"));
  assertEqual(errors.length, 1);
});

test('positive: negative returns 1 error', () => {
  const errors = collectErrors(positive("-3"));
  assertEqual(errors.length, 1);
});

// pattern
test('pattern: matching pattern returns 0 errors', () => {
  const errors = collectErrors(pattern_("^\\d+$")("err")("123"));
  assertEqual(errors.length, 0);
});

test('pattern: non-matching pattern returns 1 error', () => {
  const errors = collectErrors(pattern_("^\\d+$")("err")("abc"));
  assertEqual(errors.length, 1);
});

console.log(`\nPassed: ${passed}, Failed: ${failed}, Total: ${passed + failed}`);
process.exit(failed > 0 ? 1 : 0);
