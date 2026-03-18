/**
 * Serialize roundtrip tests for Agdelte.FFI.Shared
 */

import S from '../_build/jAgda.Agdelte.FFI.Shared.mjs';

// Agda Serialize record: fields accessed via Serialize.encode(instance) / Serialize.decode(instance)
const getEnc = (inst) => S.Serialize.encode(inst);
const getDec = (inst) => S.Serialize.decode(inst);

// Instance records
const sString = S.serializeString;
const sBool   = S.serializeBool;
const sNat    = S.serializeNat;
const sMaybeS = S.serializeMaybe(null)(sString);
const sListS  = S.serializeList(null)(sString);
const sResultSS = S.serializeResult(null)(null)(sString)(sString);

let passed = 0, failed = 0;

function test(name, fn) {
  try { fn(); console.log(`\u2713 ${name}`); passed++; }
  catch (e) { console.log(`\u2717 ${name}: ${e.message}`); failed++; }
}

function assert(cond, msg) { if (!cond) throw new Error(msg || 'assertion failed'); }
function assertEqual(a, b, msg) { if (a !== b) throw new Error(msg || `${JSON.stringify(a)} !== ${JSON.stringify(b)}`); }

const matchMaybe = (m) => m({ just: x => ({ tag: 'just', value: x }), nothing: () => ({ tag: 'nothing' }) });
// Agda Bool compiles to JS boolean, not Scott. Pattern match via ternary.
const matchBool = (b) => (typeof b === 'function') ? b({ "true": () => true, "false": () => false }) : b;
const matchResult = (r) => r({ ok: v => ({ tag: 'ok', value: v }), err: e => ({ tag: 'err', error: e }) });

function collectList(list) {
  const arr = []; let cur = list; let done = false;
  while (!done) { cur({ '[]': () => { done = true; }, '_∷_': (h, t) => { arr.push(h); cur = t; } }); }
  return arr;
}

// Scott constructors
// Agda Bool compiles to JS true/false (not Scott-encoded)
const scottTrue  = true;
const scottFalse = false;
const scottJust  = (x) => (c) => c.just(x);
const scottNothing = (c) => c.nothing();
const scottOk  = (x) => (c) => c.ok(x);
const scottErr = (x) => (c) => c.err(x);
const scottNil = (c) => c['[]']();
const scottCons = (h, t) => (c) => c['_∷_'](h, t);

// ─── String ─────────────────────────────────────────────────────────

console.log('\n=== Serialize String ===\n');

test('String: roundtrip "hello"', () => {
  const encoded = getEnc(sString)("hello");
  assertEqual(encoded, "hello");
  const decoded = matchMaybe(getDec(sString)(encoded));
  assertEqual(decoded.tag, 'just');
  assertEqual(decoded.value, "hello");
});

test('String: roundtrip empty', () => {
  const r = matchMaybe(getDec(sString)(getEnc(sString)("")));
  assertEqual(r.tag, 'just');
  assertEqual(r.value, "");
});

test('String: roundtrip special chars', () => {
  for (const s of ["a:b", "new\nline", "tab\there", 'qu"ote']) {
    const r = matchMaybe(getDec(sString)(getEnc(sString)(s)));
    assertEqual(r.tag, 'just');
    assertEqual(r.value, s);
  }
});

// ─── Bool ───────────────────────────────────────────────────────────

console.log('\n=== Serialize Bool ===\n');

test('Bool: encode true', () => { assertEqual(getEnc(sBool)(scottTrue), "true"); });
test('Bool: encode false', () => { assertEqual(getEnc(sBool)(scottFalse), "false"); });

test('Bool: decode "true"', () => {
  const r = matchMaybe(getDec(sBool)("true"));
  assertEqual(r.tag, 'just');
  assertEqual(matchBool(r.value), true);
});

test('Bool: decode "false"', () => {
  const r = matchMaybe(getDec(sBool)("false"));
  assertEqual(r.tag, 'just');
  assertEqual(matchBool(r.value), false);
});

test('Bool: decode invalid', () => {
  assertEqual(matchMaybe(getDec(sBool)("maybe")).tag, 'nothing');
});

// ─── ℕ ──────────────────────────────────────────────────────────────

console.log('\n=== Serialize ℕ ===\n');

test('ℕ: roundtrip 0', () => {
  const r = matchMaybe(getDec(sNat)(getEnc(sNat)(0n)));
  assertEqual(r.tag, 'just');
  assertEqual(r.value, 0n);
});

test('ℕ: roundtrip 42', () => {
  const r = matchMaybe(getDec(sNat)(getEnc(sNat)(42n)));
  assertEqual(r.tag, 'just');
  assertEqual(r.value, 42n);
});

test('ℕ: decode invalid', () => { assertEqual(matchMaybe(getDec(sNat)("abc")).tag, 'nothing'); });
test('ℕ: decode negative', () => { assertEqual(matchMaybe(getDec(sNat)("-5")).tag, 'nothing'); });

// ─── Maybe ──────────────────────────────────────────────────────────

console.log('\n=== Serialize Maybe ===\n');

test('Maybe String: encode just', () => { assertEqual(getEnc(sMaybeS)(scottJust("hi")), "just:hi"); });
test('Maybe String: encode nothing', () => { assertEqual(getEnc(sMaybeS)(scottNothing), "nothing"); });

test('Maybe String: decode just', () => {
  const r = matchMaybe(getDec(sMaybeS)("just:hello"));
  assertEqual(r.tag, 'just');
  const inner = matchMaybe(r.value);
  assertEqual(inner.tag, 'just');
  assertEqual(inner.value, "hello");
});

test('Maybe String: decode nothing', () => {
  const r = matchMaybe(getDec(sMaybeS)("nothing"));
  assertEqual(r.tag, 'just');
  assertEqual(matchMaybe(r.value).tag, 'nothing');
});

test('Maybe String: decode invalid', () => { assertEqual(matchMaybe(getDec(sMaybeS)("garbage")).tag, 'nothing'); });

// ─── List ───────────────────────────────────────────────────────────

console.log('\n=== Serialize List ===\n');

test('List String: encode empty', () => { assertEqual(getEnc(sListS)(scottNil), ""); });

test('List String: encode [a, bb, ccc]', () => {
  const list = scottCons("a", scottCons("bb", scottCons("ccc", scottNil)));
  assertEqual(getEnc(sListS)(list), "1:a2:bb3:ccc");
});

test('List String: roundtrip [hello, world]', () => {
  const list = scottCons("hello", scottCons("world", scottNil));
  const encoded = getEnc(sListS)(list);
  const r = matchMaybe(getDec(sListS)(encoded));
  assertEqual(r.tag, 'just');
  const arr = collectList(r.value);
  assertEqual(arr.length, 2);
  assertEqual(arr[0], "hello");
  assertEqual(arr[1], "world");
});

test('List String: roundtrip with colons and numbers', () => {
  const list = scottCons("a:b", scottCons("123", scottCons("", scottNil)));
  const encoded = getEnc(sListS)(list);
  const r = matchMaybe(getDec(sListS)(encoded));
  assertEqual(r.tag, 'just');
  const arr = collectList(r.value);
  assertEqual(arr.length, 3);
  assertEqual(arr[0], "a:b");
  assertEqual(arr[1], "123");
  assertEqual(arr[2], "");
});

test('List String: decode empty', () => {
  const r = matchMaybe(getDec(sListS)(""));
  assertEqual(r.tag, 'just');
  assertEqual(collectList(r.value).length, 0);
});

// ─── Result ─────────────────────────────────────────────────────────

console.log('\n=== Serialize Result ===\n');

test('Result: encode ok', () => { assertEqual(getEnc(sResultSS)(scottOk("win")), "ok:win"); });
test('Result: encode err', () => { assertEqual(getEnc(sResultSS)(scottErr("fail")), "err:fail"); });

test('Result: decode ok', () => {
  const r = matchMaybe(getDec(sResultSS)("ok:hello"));
  assertEqual(r.tag, 'just');
  const res = matchResult(r.value);
  assertEqual(res.tag, 'ok');
  assertEqual(res.value, "hello");
});

test('Result: decode err', () => {
  const r = matchMaybe(getDec(sResultSS)("err:oops"));
  assertEqual(r.tag, 'just');
  const res = matchResult(r.value);
  assertEqual(res.tag, 'err');
  assertEqual(res.error, "oops");
});

test('Result: decode invalid', () => { assertEqual(matchMaybe(getDec(sResultSS)("garbage")).tag, 'nothing'); });

// ─── Results ────────────────────────────────────────────────────────

console.log(`\nPassed: ${passed}, Failed: ${failed}, Total: ${passed + failed}`);
process.exit(failed > 0 ? 1 : 0);
