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

// ========================================
// DateTime Edge Cases (A53, T4)
// ========================================

console.log('\n=== DateTime Edge Cases ===\n');

test('leap year: Feb 29 2024', () => {
  const d = new Date(2024, 1, 29); // Feb 29
  assertEqual(getMonth(d), 2n, 'February');
  assertEqual(getDay(d), 29n, 'day 29');
});

test('leap year: Feb 29 via ISO', () => {
  const result = matchMaybe(fromISOString("2024-02-29T00:00:00Z"));
  assert(result !== null, 'Feb 29 2024 should parse');
  assertEqual(getDay(result), 29n);
});

test('non-leap year: Feb 28 2023', () => {
  const d = new Date(2023, 1, 28);
  assertEqual(getDay(d), 28n, '2023 is not leap year, max day is 28');
});

test('epoch boundary: Jan 1 1970', () => {
  const d = fromMillis(0n);
  assert(d instanceof Date);
  // getTime should be 0 (UTC epoch)
  assertEqual(d.getTime(), 0);
});

test('negative millis: dates before epoch', () => {
  // Dec 31 1969 in UTC is -86400000 ms
  const d = fromMillis(-86400000n);
  assert(d instanceof Date);
  assert(d.getTime() < 0, 'should be before epoch');
});

test('diffDates: same date = 0', () => {
  const d = new Date(2024, 5, 15);
  const dur = extractDuration(diffDates(d)(d));
  assertEqual(dur, 0n, 'same date diff should be 0');
});

test('diffDates: reverse order gives absolute value', () => {
  const d1 = new Date(2024, 0, 2);
  const d2 = new Date(2024, 0, 1);
  const dur = extractDuration(diffDates(d1)(d2));
  // diffDates computes |d2 - d1| or d1 - d2, result is positive
  assertEqual(dur, 86400000n, 'reverse order gives positive (absolute) diff');
});

test('isBefore: same date returns false', () => {
  const d = new Date(2024, 0, 1);
  assertEqual(matchBool(isBefore(d)(d)), false, 'same date is not before itself');
});

test('isAfter: same date returns false', () => {
  const d = new Date(2024, 0, 1);
  assertEqual(matchBool(isAfter(d)(d)), false, 'same date is not after itself');
});

test('addDuration then subDuration is identity', () => {
  const d = new Date(2024, 6, 15, 12, 30, 0);
  const dur = mkDuration(3600000n); // 1 hour
  const added = addDuration(dur)(d);
  const result = subDuration(dur)(added);
  assertEqual(result.getTime(), d.getTime(), 'add then sub should be identity');
});

test('format: year 999 (3 digits)', () => {
  const d = new Date(999, 5, 15);
  const formatted = format("YYYY")(d);
  // Date constructor with year < 100 maps to 1900+year, but 999 is fine
  assert(formatted.includes('999'), `should contain 999, got: ${formatted}`);
});

console.log(`\nPassed: ${passed}, Failed: ${failed}, Total: ${passed + failed}`);
process.exit(failed > 0 ? 1 : 0);
