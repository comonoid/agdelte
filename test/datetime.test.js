/**
 * Agdelte DateTime FFI Tests
 */

import DateTimeModule from '../_build/jAgda.Agdelte.DateTime.mjs';

const { format, fromISOString, fromMillis, addDuration, subDuration,
        diffDates, isBefore, isAfter, parse,
        getYear, getMonth, getDay } = DateTimeModule;

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
const matchBool = (b) => b({"true": () => true, "false": () => false});
const matchMaybe = (m) => m({just: x => x, nothing: () => null});

// Duration helpers (object-encoded from diffDates, function-encoded for mkDuration)
const mkDuration = (ms) => ({"mkDuration": cb => cb["mkDuration"](ms)});
const extractDuration = (dur) => dur["mkDuration"]({mkDuration: ms => ms});

// ========================================
// Tests
// ========================================

console.log('\n=== DateTime FFI Tests ===\n');

// format
test('format YYYY-MM-DD', () => {
  assertEqual(format("YYYY-MM-DD")(new Date(2024, 0, 15)), "2024-01-15");
});

test('format HH:mm:ss', () => {
  assertEqual(format("HH:mm:ss")(new Date(2024, 0, 1, 9, 5, 3)), "09:05:03");
});

test('format global replacement', () => {
  assertEqual(format("YYYY to YYYY")(new Date(2024, 0, 1)), "2024 to 2024");
});

// fromISOString
test('fromISOString: valid ISO date', () => {
  const result = matchMaybe(fromISOString("2024-01-15T00:00:00Z"));
  assert(result !== null, "should return just");
  assert(result instanceof Date, "should be a Date");
});

test('fromISOString: invalid date returns nothing', () => {
  const result = matchMaybe(fromISOString("not-a-date"));
  assertEqual(result, null);
});

// parse
test('parse: valid date string', () => {
  const result = matchMaybe(parse("2024-01-15"));
  assert(result !== null, "should return just");
});

test('parse: garbage returns nothing', () => {
  const result = matchMaybe(parse("garbage"));
  assertEqual(result, null);
});

// addDuration / subDuration
test('addDuration: adds milliseconds', () => {
  const d = new Date(2024, 0, 1);
  const result = addDuration(mkDuration(1000n))(d);
  assertEqual(result.getTime(), d.getTime() + 1000);
});

test('subDuration: subtracts milliseconds', () => {
  const d = new Date(2024, 0, 1);
  const result = subDuration(mkDuration(1000n))(d);
  assertEqual(result.getTime(), d.getTime() - 1000);
});

// diffDates
test('diffDates: 24 hours difference', () => {
  const d1 = new Date(2024, 0, 1);
  const d2 = new Date(2024, 0, 2);  // 24h later
  const dur = extractDuration(diffDates(d1)(d2));
  assertEqual(dur, 86400000n);
});

// isBefore / isAfter
test('isBefore: earlier date', () => {
  const d1 = new Date(2024, 0, 1);
  const d2 = new Date(2024, 0, 2);
  assertEqual(matchBool(isBefore(d1)(d2)), true);
});

test('isBefore: later date returns false', () => {
  const d1 = new Date(2024, 0, 2);
  const d2 = new Date(2024, 0, 1);
  assertEqual(matchBool(isBefore(d1)(d2)), false);
});

test('isAfter: later date', () => {
  const d1 = new Date(2024, 0, 2);
  const d2 = new Date(2024, 0, 1);
  assertEqual(matchBool(isAfter(d1)(d2)), true);
});

// getYear / getMonth / getDay
test('getYear returns BigInt', () => {
  assertEqual(getYear(new Date(2024, 0, 15)), 2024n);
});

test('getMonth returns 1-indexed BigInt', () => {
  assertEqual(getMonth(new Date(2024, 0, 15)), 1n);
});

test('getDay returns BigInt', () => {
  assertEqual(getDay(new Date(2024, 0, 15)), 15n);
});

// fromMillis
test('fromMillis: creates date from BigInt millis', () => {
  const ms = BigInt(new Date(2024, 0, 1).getTime());
  const result = fromMillis(ms);
  assert(result instanceof Date, "should be a Date");
  assertEqual(result.getFullYear(), 2024);
});

console.log(`\nPassed: ${passed}, Failed: ${failed}, Total: ${passed + failed}`);
process.exit(failed > 0 ? 1 : 0);
