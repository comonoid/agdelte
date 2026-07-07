/**
 * Runtime regression tests for the 2026-07-07 fixes (found by the cxm-ui live smoke, previously
 * guarded ONLY downstream — аудит cxm-ui №6). Each block pins one fix IN THIS REPO:
 *   1. deepEqual understands Agda 2.9 OBJECT-encoded Scott values and native arrays.
 *   2. agdaHeadersToObj accepts both pair encodings (callable + object).
 *   3. foreachKeyed re-renders a row whose item changed under the SAME key (stale-row fix).
 *   4. value-binding diffs against the LIVE input value (controlled-input desync fix).
 *   5. httpGetH/httpPostH deliver the non-2xx response BODY to the error callback.
 *
 * Needs: npm run build:runtime-probe (examples/RuntimeFixesProbe.agda → _build).
 */
import { Window } from 'happy-dom';

const window = new Window({ url: 'http://localhost:3000' });
for (const k of ['document', 'HTMLElement', 'Element', 'Node', 'Text', 'Comment',
  'DOMException', 'MutationObserver', 'KeyboardEvent', 'MouseEvent']) globalThis[k] = window[k];
globalThis.window = window;
globalThis.requestAnimationFrame = (cb) => setTimeout(cb, 0);
globalThis.cancelAnimationFrame = (id) => clearTimeout(id);

const { runReactiveApp, deepEqual, agdaHeadersToObj } = await import('../runtime/reactive.js');

let passed = 0, failed = 0;
const test = (name, fn) => { try { fn(); console.log(`✓ ${name}`); passed++; }
  catch (e) { console.log(`✗ ${name}: ${e.message}`); failed++; } };
const assert = (c, m) => { if (!c) throw new Error(m || 'assertion failed'); };
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

// ─── 1. deepEqual: object-encoded Scott values + arrays ─────────────────────

const objPair = (a, b) => ({ '_,_': (cb) => cb['_,_'](a, b) });   // Agda 2.9 record encoding
const fnPair = (a, b) => (cb) => cb['_,_'](a, b);                 // older callable encoding

test('deepEqual: object-Scott equal by structure (fresh closures)', () => {
  assert(deepEqual(objPair(1n, 'x'), objPair(1n, 'x')), 'structurally equal must be equal');
});
test('deepEqual: object-Scott unequal contents detected', () => {
  assert(!deepEqual(objPair(1n, 'x'), objPair(1n, 'y')), 'different field must differ');
});
test('deepEqual: native arrays elementwise', () => {
  assert(deepEqual([objPair(1n, 'a')], [objPair(1n, 'a')]), 'array of records equal');
  assert(!deepEqual([1n, 2n], [1n, 3n]), 'different element');
  assert(!deepEqual([1n], [1n, 2n]), 'different length');
});

// ─── 2. agdaHeadersToObj: both pair encodings ───────────────────────────────

test('agdaHeadersToObj: callable pairs', () => {
  const h = agdaHeadersToObj([fnPair('A', '1'), fnPair('B', '2')]);
  assert(h.A === '1' && h.B === '2', JSON.stringify(h));
});
test('agdaHeadersToObj: object-encoded pairs (Agda 2.9)', () => {
  const h = agdaHeadersToObj([objPair('Authorization', 'Bearer t')]);
  assert(h.Authorization === 'Bearer t', JSON.stringify(h));
});

// ─── 3–5. Probe app E2E (compiled from examples/RuntimeFixesProbe.agda) ─────

let probe = null;
try {
  probe = (await import('../_build/jAgda.RuntimeFixesProbe.mjs')).default;
} catch {
  console.log('✗ probe module missing — run `npm run build:runtime-probe` first');
  failed++;
}

if (probe) {
  // fetch mock: /err → 409 with an error-envelope body; /ok → 200
  let lastHeaders = null;
  let mode = 'err';
  globalThis.fetch = (url, opts) => {
    lastHeaders = opts && opts.headers;
    const ok = mode === 'ok';
    return Promise.resolve({
      ok, status: ok ? 200 : 409,
      text: () => Promise.resolve(ok ? '{"data":{"ok":true}}' : '{"error":{"code":"conflict"}}'),
    });
  };

  const stage = document.createElement('div');
  document.body.appendChild(stage);
  const app = await runReactiveApp(probe, stage);

  // 3. keyed re-render on content change (same key)
  const rowsBefore = [...stage.querySelectorAll('.row')].map((r) => r.textContent);
  stage.querySelector('.bump').click();
  await sleep(50);
  const rowsAfter = [...stage.querySelectorAll('.row')].map((r) => r.textContent);
  test('foreachKeyed: row re-renders when item content changes under same key', () => {
    assert(rowsBefore[0] === 'a', `before: ${rowsBefore}`);
    assert(rowsAfter[0] === 'A!', `after: ${rowsAfter} (stale row!)`);
    assert(rowsAfter[1] === 'b', 'untouched row intact');
  });

  // 4. controlled input: user-typed value + same-tick submit round-trip → cleared
  const inp = stage.querySelector('.inp');
  inp.value = 'typed';
  inp.dispatchEvent(new window.Event('input', { bubbles: true }));
  stage.querySelector('.submit').click();               // тот же тик — intra-batch round-trip
  await sleep(50);
  test('value-binding: intra-batch round-trip clears the LIVE input value', () => {
    assert(inp.value === '', `input still "${inp.value}" (controlled-input desync!)`);
  });

  // 5. http error body + header encoding end-to-end
  stage.querySelector('.fire').click();
  await sleep(50);
  test('httpPostH: non-2xx BODY reaches the error callback', () => {
    const res = stage.querySelector('.res').textContent;
    assert(res === 'err:{"error":{"code":"conflict"}}', `got "${res}"`);
  });
  test('httpPostH: Agda-built header list survives agdaHeadersToObj', () => {
    assert(lastHeaders && lastHeaders['X-Probe'] === '1', JSON.stringify(lastHeaders));
  });

  mode = 'ok';
  stage.querySelector('.fire').click();
  await sleep(50);
  test('httpPostH: 2xx body reaches the ok callback', () => {
    const res = stage.querySelector('.res').textContent;
    assert(res === 'ok:{"data":{"ok":true}}', `got "${res}"`);
  });

  if (app && app.destroy) app.destroy();
}

console.log(`\nPassed: ${passed}, Failed: ${failed}`);
process.exit(failed === 0 ? 0 : 1);
