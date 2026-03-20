/**
 * Tests for HTTP with headers (httpGetH/httpPostH), Auth.Client, and agdaHeadersToObj.
 * Run: node test/auth-http.test.js
 */

import Cmd from '../_build/jAgda.Agdelte.Core.Cmd.mjs';
import Task from '../_build/jAgda.Agdelte.Core.Task.mjs';
import AuthClient from '../_build/jAgda.Agdelte.Auth.Client.mjs';
import List from '../_build/jAgda.Agda.Builtin.List.mjs';
import agdaRTS from '../_build/agda-rts.mjs';

// ========================================
// Test runner
// ========================================

let passed = 0;
let failed = 0;

function test(name, fn) {
  try {
    fn();
    console.log(`  ✓ ${name}`);
    passed++;
  } catch (e) {
    console.log(`  ✗ ${name}: ${e.message}`);
    failed++;
  }
}

function assert(cond, msg = 'Assertion failed') {
  if (!cond) throw new Error(msg);
}

function assertEqual(actual, expected, msg) {
  if (actual !== expected) throw new Error(msg || `Expected ${JSON.stringify(expected)}, got ${JSON.stringify(actual)}`);
}

// ========================================
// Helpers
// ========================================

// Agda List → JS array. Handles both:
// - JS array (--js-optimize compiles small lists as native arrays)
// - Scott-encoded function (larger/dynamic lists)
function listToArray(agdaList) {
  if (Array.isArray(agdaList)) return agdaList;
  const items = [];
  let cur = agdaList;
  for (let i = 0; i < 100; i++) {
    if (typeof cur !== 'function') break;
    let done = false;
    cur({
      '[]': () => { done = true; },
      '_∷_': (head, tail) => { items.push(head); cur = tail; }
    });
    if (done) break;
  }
  return items;
}

function pairToObj(pair) {
  let k = '', v = '';
  if (typeof pair === 'function') {
    pair({ '_,_': (a, b) => { k = a; v = b; } });
  } else if (pair && pair['_,_']) {
    pair['_,_']({ '_,_': (a, b) => { k = a; v = b; } });
  }
  return { k, v };
}

function cmdName(cmd) {
  let name = 'unknown';
  const handler = {};
  for (const n of ['ε', '_<>_', 'delay', 'httpGet', 'httpPost', 'httpGetH', 'httpPostH',
    'attempt', 'focus', 'blur', 'scrollTo', 'scrollIntoView', 'writeClipboard', 'readClipboard',
    'getItem', 'setItem', 'removeItem', 'wsSend', 'channelSend', 'freeBuffer', 'touchBuffer',
    'callMethod', 'setProp', 'getProp', 'mediaSourceInit', 'mediaSourceAppend', 'mediaSourceEnd',
    'pushUrl', 'replaceUrl', 'back', 'forward']) {
    handler[n] = (...args) => { name = n; };
  }
  try { cmd(handler); } catch (e) { name = 'error'; }
  return name;
}

function cmdHttpGetH(cmd) {
  let url = '', headers = null;
  const handler = {};
  for (const n of ['ε', '_<>_', 'delay', 'httpGet', 'httpPost', 'httpPostH',
    'attempt', 'focus', 'blur', 'scrollTo', 'scrollIntoView', 'writeClipboard', 'readClipboard',
    'getItem', 'setItem', 'removeItem', 'wsSend', 'channelSend', 'freeBuffer', 'touchBuffer',
    'callMethod', 'setProp', 'getProp', 'mediaSourceInit', 'mediaSourceAppend', 'mediaSourceEnd',
    'pushUrl', 'replaceUrl', 'back', 'forward']) {
    handler[n] = () => {};
  }
  handler['httpGetH'] = (u, h, onOk, onErr) => { url = u; headers = h; };
  cmd(handler);
  return { url, headers };
}

function cmdHttpPostH(cmd) {
  let url = '', headers = null, body = '';
  const handler = {};
  for (const n of ['ε', '_<>_', 'delay', 'httpGet', 'httpPost', 'httpGetH',
    'attempt', 'focus', 'blur', 'scrollTo', 'scrollIntoView', 'writeClipboard', 'readClipboard',
    'getItem', 'setItem', 'removeItem', 'wsSend', 'channelSend', 'freeBuffer', 'touchBuffer',
    'callMethod', 'setProp', 'getProp', 'mediaSourceInit', 'mediaSourceAppend', 'mediaSourceEnd',
    'pushUrl', 'replaceUrl', 'back', 'forward']) {
    handler[n] = () => {};
  }
  handler['httpPostH'] = (u, h, b, onOk, onErr) => { url = u; headers = h; body = b; };
  cmd(handler);
  return { url, headers, body };
}

// ========================================
// 1. Cmd constructors
// ========================================

console.log('\n=== Cmd httpGetH/httpPostH ===\n');

test('Cmd.httpGetH produces httpGetH command', () => {
  const hdrs = List["List"]["_∷_"](
    { '_,_': cb => cb['_,_']('X-Custom', 'value') },
    List["List"]["[]"]
  );
  const cmd = Cmd["Cmd"]["httpGetH"]("/api/test")(hdrs)(x => x)(x => x);
  assertEqual(cmdName(cmd), 'httpGetH');
});

test('Cmd.httpPostH produces httpPostH command', () => {
  const hdrs = List["List"]["_∷_"](
    { '_,_': cb => cb['_,_']('Authorization', 'Bearer tok') },
    List["List"]["[]"]
  );
  const cmd = Cmd["Cmd"]["httpPostH"]("/api/test")(hdrs)('{"a":1}')(x => x)(x => x);
  assertEqual(cmdName(cmd), 'httpPostH');
});

// ========================================
// 2. Auth.Client
// ========================================

console.log('\n=== Auth.Client ===\n');

test('saveToken produces setItem cmd', () => {
  const cmd = AuthClient["saveToken"](null)("my-jwt-token");
  assertEqual(cmdName(cmd), 'setItem');
});

test('clearToken produces removeItem cmd', () => {
  const cmd = AuthClient["clearToken"](null);
  assertEqual(cmdName(cmd), 'removeItem');
});

test('loadToken produces getItem cmd', () => {
  const cmd = AuthClient["loadToken"](null)(x => x);
  assertEqual(cmdName(cmd), 'getItem');
});

test('authGet produces httpGetH with Bearer header', () => {
  const cmd = AuthClient["authGet"](null)("/api/courses")("my-token")(x => x)(x => x);
  assertEqual(cmdName(cmd), 'httpGetH');
  const { url, headers } = cmdHttpGetH(cmd);
  assertEqual(url, '/api/courses');
  const hdrs = listToArray(headers).map(pairToObj);
  assertEqual(hdrs.length, 1);
  assertEqual(hdrs[0].k, 'Authorization');
  assertEqual(hdrs[0].v, 'Bearer my-token');
});

test('authPost produces httpPostH with Bearer + JSON headers', () => {
  const cmd = AuthClient["authPost"](null)("/api/buy")("tok123")('{"courseId":"c1"}')(x => x)(x => x);
  assertEqual(cmdName(cmd), 'httpPostH');
  const { url, headers, body } = cmdHttpPostH(cmd);
  assertEqual(url, '/api/buy');
  assertEqual(body, '{"courseId":"c1"}');
  const hdrs = listToArray(headers).map(pairToObj);
  assertEqual(hdrs.length, 2);
  assertEqual(hdrs[0].k, 'Authorization');
  assertEqual(hdrs[0].v, 'Bearer tok123');
  assertEqual(hdrs[1].k, 'Content-Type');
  assertEqual(hdrs[1].v, 'application/json');
});

test('loginCmd produces httpPostH with JSON body', () => {
  const cmd = AuthClient["loginCmd"](null)("/api/login")("a@b.com")("pass123")(x => x)(x => x);
  assertEqual(cmdName(cmd), 'httpPostH');
  const { url, body } = cmdHttpPostH(cmd);
  assertEqual(url, '/api/login');
  assert(body.includes('"email":"a@b.com"'), 'body should contain email');
  assert(body.includes('"password":"pass123"'), 'body should contain password');
});

test('registerCmd same as loginCmd', () => {
  const cmd = AuthClient["registerCmd"](null)("/api/register")("x@y.com")("secret")(x => x)(x => x);
  const { url, body } = cmdHttpPostH(cmd);
  assertEqual(url, '/api/register');
  assert(body.includes('"email":"x@y.com"'));
});

// ========================================
// 3. authHeaders structure
// ========================================

console.log('\n=== Auth headers ===\n');

test('authHeaders creates single Authorization header', () => {
  const hdrs = listToArray(AuthClient["authHeaders"]("tok")).map(pairToObj);
  assertEqual(hdrs.length, 1);
  assertEqual(hdrs[0].k, 'Authorization');
  assertEqual(hdrs[0].v, 'Bearer tok');
});

test('authJsonHeaders creates Authorization + Content-Type', () => {
  const hdrs = listToArray(AuthClient["authJsonHeaders"]("tok")).map(pairToObj);
  assertEqual(hdrs.length, 2);
  assertEqual(hdrs[0].k, 'Authorization');
  assertEqual(hdrs[1].k, 'Content-Type');
  assertEqual(hdrs[1].v, 'application/json');
});

// ========================================
// 4. mapCmd preserves httpGetH/httpPostH
// ========================================

console.log('\n=== mapCmd with headers ===\n');

test('mapCmd httpGetH wraps callbacks', () => {
  const hdrs = List["List"]["_∷_"](
    { '_,_': cb => cb['_,_']('X-Test', 'val') },
    List["List"]["[]"]
  );
  const original = Cmd["Cmd"]["httpGetH"]("/url")(hdrs)(s => ({ tag: 'ok', val: s }))(e => ({ tag: 'err', val: e }));
  const mapped = Cmd["mapCmd"](null)(null)(x => ({ wrapped: x }))(original);
  assertEqual(cmdName(mapped), 'httpGetH');
});

test('mapCmd httpPostH wraps callbacks', () => {
  const hdrs = List["List"]["[]"];
  const original = Cmd["Cmd"]["httpPostH"]("/url")(hdrs)("body")(s => s)(e => e);
  const mapped = Cmd["mapCmd"](null)(null)(x => ({ wrapped: x }))(original);
  assertEqual(cmdName(mapped), 'httpPostH');
});

// ========================================
// Summary
// ========================================

console.log(`\n${'='.repeat(40)}`);
console.log(`Results: ${passed} passed, ${failed} failed`);
process.exit(failed > 0 ? 1 : 0);
