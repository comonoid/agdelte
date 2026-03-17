/**
 * Tests for cloneSlot handling of both function-format and object-format
 * mutable wrappers.
 *
 * Since wrapMutable and cloneSlot are module-internal (not exported),
 * we replicate their logic inline here, mirroring reactive.js exactly.
 */

import { strict as assert } from 'node:assert';

// ─────────────────────────────────────────────────────────────────────
// Replicated helpers from agda-values.js
// ─────────────────────────────────────────────────────────────────────

const _slotProbe = new Proxy({}, {
  get(_, name) { return (...args) => args; }
});

function probeSlots(model) {
  if (!model) return null;
  if (typeof model === 'function') {
    try {
      const result = model(_slotProbe);
      return Array.isArray(result) ? result : null;
    } catch { return null; }
  }
  if (typeof model === 'object') {
    const keys = Object.keys(model);
    if (keys.length === 1 && typeof model[keys[0]] === 'function') {
      try { return model[keys[0]](_slotProbe); } catch { return null; }
    }
  }
  return null;
}

function probeCtor(model) {
  if (!model) return null;
  if (typeof model === 'function') {
    let ctor = null;
    try {
      model(new Proxy({}, {
        get(_, name) { return (...args) => { ctor = name; }; }
      }));
    } catch { return null; }
    return ctor;
  }
  if (typeof model === 'object') {
    const keys = Object.keys(model);
    if (keys.length === 1 && typeof model[keys[0]] === 'function') {
      return keys[0];
    }
  }
  return null;
}

// ─────────────────────────────────────────────────────────────────────
// Replicated wrapMutable from reactive.js
// ─────────────────────────────────────────────────────────────────────

function wrapMutable(model, _visited) {
  if (model && model._slots) return model;
  if (model === null || model === undefined) return model;
  if (typeof model !== 'function' && typeof model !== 'object') return model;

  if (!_visited) _visited = new WeakMap();
  if (_visited.has(model)) return _visited.get(model);

  const args = probeSlots(model);
  const ctor = probeCtor(model);
  if (!args || !ctor) return model;

  const slots = [];
  let wrapper;
  if (typeof model === 'function') {
    wrapper = (cases) => cases[ctor](...slots);
  } else {
    wrapper = { [ctor]: (c) => c[ctor](...slots) };
  }
  wrapper._slots = slots;
  wrapper._ctor = ctor;
  _visited.set(model, wrapper);

  for (const a of args) {
    slots.push(
      (typeof a === 'function' || (typeof a === 'object' && a !== null))
        ? wrapMutable(a, _visited)
        : a
    );
  }

  return wrapper;
}

// ─────────────────────────────────────────────────────────────────────
// Replicated cloneSlot from reactive.js
// ─────────────────────────────────────────────────────────────────────

function cloneSlot(s) {
  if (s && s._slots && s._ctor) {
    const clonedSlots = s._slots.map(c => {
      if (c && c._slots && c._ctor) return cloneSlot(c);
      if (typeof c === 'object' && c !== null) {
        try { return structuredClone(c); } catch { return c; }
      }
      return c;
    });
    const ctor = s._ctor;
    if (typeof s === 'function') {
      const w = (cases) => cases[ctor](...clonedSlots);
      w._slots = clonedSlots;
      w._ctor = ctor;
      return w;
    } else {
      const w = { [ctor]: (c) => c[ctor](...clonedSlots) };
      w._slots = clonedSlots;
      w._ctor = ctor;
      return w;
    }
  }
  if (!s) return s;
  if (typeof s === 'object' && s !== null) {
    try { return structuredClone(s); } catch { return s; }
  }
  return s;
}

// ─────────────────────────────────────────────────────────────────────
// Helper: extract values from a Scott-encoded model via a probe cases object
// ─────────────────────────────────────────────────────────────────────

function extractValues(model) {
  const probe = new Proxy({}, {
    get(_, name) {
      return (...args) => ({ ctor: name, args });
    }
  });
  if (typeof model === 'function') {
    return model(probe);
  }
  if (typeof model === 'object') {
    const keys = Object.keys(model).filter(k => k !== '_slots' && k !== '_ctor');
    if (keys.length === 1 && typeof model[keys[0]] === 'function') {
      return model[keys[0]](probe);
    }
  }
  throw new Error('Cannot extract values from model');
}

// ─────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────

let passed = 0;
let failed = 0;

function test(name, fn) {
  try {
    fn();
    passed++;
    console.log(`  PASS: ${name}`);
  } catch (e) {
    failed++;
    console.log(`  FAIL: ${name}`);
    console.log(`        ${e.message}`);
  }
}

console.log('--- cloneSlot format tests ---\n');

// ═══════════════════════════════════════════════════════════════════
// 1. Function-format Scott-encoded model
// ═══════════════════════════════════════════════════════════════════

console.log('1. Function-format model');

const fnModel = (c) => c.mkModel(1, "hello", 2n);
const fnWrapped = wrapMutable(fnModel);
const fnClone = cloneSlot(fnWrapped);

test('wrapped is a function', () => {
  assert.equal(typeof fnWrapped, 'function');
});

test('clone is a function', () => {
  assert.equal(typeof fnClone, 'function');
});

test('clone has different _slots array', () => {
  assert.notStrictEqual(fnClone._slots, fnWrapped._slots);
});

test('clone has same _ctor', () => {
  assert.equal(fnClone._ctor, fnWrapped._ctor);
});

test('clone callable form returns same values', () => {
  const origVals = extractValues(fnWrapped);
  const cloneVals = extractValues(fnClone);
  assert.equal(origVals.ctor, cloneVals.ctor);
  assert.deepStrictEqual(origVals.args, cloneVals.args);
});

test('mutating clone _slots[0] does NOT affect original', () => {
  fnClone._slots[0] = 999;
  assert.equal(fnWrapped._slots[0], 1);
  assert.equal(fnClone._slots[0], 999);
});

// ═══════════════════════════════════════════════════════════════════
// 2. Object-format Scott-encoded model
// ═══════════════════════════════════════════════════════════════════

console.log('\n2. Object-format model');

const objModel = { mkModel: (c) => c.mkModel(1, "hello", 2n) };
const objWrapped = wrapMutable(objModel);
const objClone = cloneSlot(objWrapped);

test('wrapped is an object (not function)', () => {
  assert.equal(typeof objWrapped, 'object');
  assert.notEqual(typeof objWrapped, 'function');
});

test('clone is an object (not function)', () => {
  assert.equal(typeof objClone, 'object');
  assert.notEqual(typeof objClone, 'function');
});

test('clone has different _slots array', () => {
  assert.notStrictEqual(objClone._slots, objWrapped._slots);
});

test('clone has same _ctor', () => {
  assert.equal(objClone._ctor, objWrapped._ctor);
});

test('clone callable form returns same values', () => {
  const origVals = extractValues(objWrapped);
  const cloneVals = extractValues(objClone);
  assert.equal(origVals.ctor, cloneVals.ctor);
  assert.deepStrictEqual(origVals.args, cloneVals.args);
});

test('mutating clone _slots[0] does NOT affect original', () => {
  objClone._slots[0] = 999;
  assert.equal(objWrapped._slots[0], 1);
  assert.equal(objClone._slots[0], 999);
});

// ═══════════════════════════════════════════════════════════════════
// 3. Nested models (model with slot containing another model)
// ═══════════════════════════════════════════════════════════════════

console.log('\n3. Nested models');

const innerFn = (c) => c.mkInner(42, "nested");
const outerFn = (c) => c.mkOuter(innerFn, "top");
const outerWrapped = wrapMutable(outerFn);
const outerClone = cloneSlot(outerWrapped);

test('outer clone has different _slots array', () => {
  assert.notStrictEqual(outerClone._slots, outerWrapped._slots);
});

test('inner model in clone has different _slots array from original inner', () => {
  const origInner = outerWrapped._slots[0];
  const cloneInner = outerClone._slots[0];
  assert.ok(origInner._slots, 'original inner should have _slots');
  assert.ok(cloneInner._slots, 'cloned inner should have _slots');
  assert.notStrictEqual(cloneInner._slots, origInner._slots);
});

test('inner clone values match original inner values', () => {
  const origInner = outerWrapped._slots[0];
  const cloneInner = outerClone._slots[0];
  assert.deepStrictEqual(origInner._slots, cloneInner._slots);
});

test('mutating nested clone slot does NOT affect original nested slot', () => {
  outerClone._slots[0]._slots[0] = 9999;
  assert.equal(outerWrapped._slots[0]._slots[0], 42);
  assert.equal(outerClone._slots[0]._slots[0], 9999);
});

// Nested with object-format inner
const innerObj = { mkInner: (c) => c.mkInner(42, "nested") };
const outerObj = { mkOuter: (c) => c.mkOuter(innerObj, "top") };
const outerObjWrapped = wrapMutable(outerObj);
const outerObjClone = cloneSlot(outerObjWrapped);

test('object-format: nested clone has different _slots', () => {
  const origInner = outerObjWrapped._slots[0];
  const cloneInner = outerObjClone._slots[0];
  assert.notStrictEqual(cloneInner._slots, origInner._slots);
});

test('object-format: nested mutation isolation', () => {
  outerObjClone._slots[0]._slots[0] = 7777;
  assert.equal(outerObjWrapped._slots[0]._slots[0], 42);
});

// ═══════════════════════════════════════════════════════════════════
// 4. Self-referential model (model with slot pointing to itself)
// ═══════════════════════════════════════════════════════════════════

console.log('\n4. Self-referential model');

// We can't create a truly self-referential Scott-encoded function directly,
// because functions are immutable closures. Instead, we build a mutable
// wrapper first, then make it self-referential by inserting itself into _slots.

const selfModel = (c) => c.mkSelf(1, "placeholder");
const selfWrapped = wrapMutable(selfModel);
// Now make it self-referential: slot[1] points to the wrapper itself
selfWrapped._slots[1] = selfWrapped;

test('self-referential: slot[1] is same object as wrapper', () => {
  assert.strictEqual(selfWrapped._slots[1], selfWrapped);
});

// NOTE: cloneSlot in reactive.js has no cycle detection (unlike wrapMutable
// which uses a WeakMap). Cloning a self-referential model causes infinite
// recursion. This test documents that limitation.
test('self-referential: cloneSlot hits infinite recursion (known limitation)', () => {
  let threw = false;
  try {
    cloneSlot(selfWrapped);
  } catch (e) {
    threw = true;
    assert.ok(
      e instanceof RangeError && /stack/i.test(e.message),
      'expected RangeError about stack size, got: ' + e.message
    );
  }
  assert.ok(threw, 'cloneSlot should throw on self-referential model');
});

// ═══════════════════════════════════════════════════════════════════
// Summary
// ═══════════════════════════════════════════════════════════════════

console.log(`\n--- Results: ${passed} passed, ${failed} failed ---`);
if (failed > 0) process.exit(1);
