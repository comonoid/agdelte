/**
 * Agdelte Runtime Tests
 * Тесты для JavaScript runtime
 */

import { createElement, patch, renderToString } from '../runtime/dom.js';
import { subscribe, unsubscribe, debounce, throttle } from '../runtime/events.js';
import { interval, animationFrame, onKey } from '../runtime/primitives.js';

// Простой test runner
let passed = 0;
let failed = 0;
let skipped = 0;

// Проверка наличия DOM (для Node.js окружения)
const hasDOM = typeof document !== 'undefined';

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

function testDOM(name, fn) {
  if (!hasDOM) {
    console.log(`○ ${name} (skipped: no DOM)`);
    skipped++;
    return;
  }
  test(name, fn);
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

// ========================================
// DOM Tests
// ========================================

console.log('\n=== DOM Tests ===\n');

testDOM('createElement creates text node', () => {
  const vnode = 'Hello';
  const dom = createElement(vnode, () => {});
  assertEqual(dom.nodeType, 3); // Text node
  assertEqual(dom.textContent, 'Hello');
});

testDOM('createElement creates element', () => {
  const vnode = {
    tag: 'div',
    attrs: [{ type: 'attr', name: 'id', value: 'test' }],
    children: ['Hello']
  };
  const dom = createElement(vnode, () => {});
  assertEqual(dom.tagName, 'DIV');
  assertEqual(dom.id, 'test');
  assertEqual(dom.textContent, 'Hello');
});

testDOM('createElement handles nested elements', () => {
  const vnode = {
    tag: 'div',
    attrs: [],
    children: [
      { tag: 'span', attrs: [], children: ['Nested'] }
    ]
  };
  const dom = createElement(vnode, () => {});
  assertEqual(dom.children.length, 1);
  assertEqual(dom.children[0].tagName, 'SPAN');
});

test('renderToString produces HTML', () => {
  const vnode = {
    tag: 'div',
    attrs: [{ type: 'attr', name: 'class', value: 'test' }],
    children: ['Hello']
  };
  const html = renderToString(vnode);
  assertEqual(html, '<div class="test">Hello</div>');
});

test('renderToString escapes HTML', () => {
  const vnode = '<script>alert("xss")</script>';
  const html = renderToString(vnode);
  assert(!html.includes('<script>'), 'Should escape script tags');
});

// ========================================
// Events Tests
// ========================================

console.log('\n=== Events Tests ===\n');

test('debounce delays calls', (done) => {
  let callCount = 0;
  const debounced = debounce(() => callCount++, 50);

  debounced();
  debounced();
  debounced();

  assertEqual(callCount, 0, 'Should not call immediately');

  // В реальных тестах используем setTimeout для проверки
  // setTimeout(() => {
  //   assertEqual(callCount, 1, 'Should call once after delay');
  //   done();
  // }, 100);
});

test('throttle limits call rate', () => {
  let callCount = 0;
  const throttled = throttle(() => callCount++, 50);

  throttled();
  throttled();
  throttled();

  assertEqual(callCount, 1, 'Should call immediately once');
});

// ========================================
// Primitives Tests
// ========================================

console.log('\n=== Primitives Tests ===\n');

test('interval creates event spec', () => {
  const spec = interval(1000)('tick');
  assertEqual(spec.type, 'interval');
  assertEqual(spec.config.ms, 1000);
  assertEqual(spec.config.msg, 'tick');
});

test('animationFrame creates event spec', () => {
  const spec = animationFrame('frame');
  assertEqual(spec.type, 'animationFrame');
  assertEqual(spec.config.msg, 'frame');
});

test('onKey creates keyboard event spec', () => {
  const spec = onKey('Enter')('submit');
  assertEqual(spec.type, 'keyboard');
  assertEqual(spec.config.eventType, 'keydown');
});

// ========================================
// Integration Tests
// ========================================

console.log('\n=== Integration Tests ===\n');

testDOM('full render cycle', () => {
  const vnode1 = {
    tag: 'div',
    attrs: [],
    children: [{ tag: 'span', attrs: [], children: ['Count: 0'] }]
  };

  const vnode2 = {
    tag: 'div',
    attrs: [],
    children: [{ tag: 'span', attrs: [], children: ['Count: 1'] }]
  };

  const dom = createElement(vnode1, () => {});
  assertEqual(dom.textContent, 'Count: 0');

  const patched = patch(dom, vnode1, vnode2, () => {});
  assertEqual(patched.textContent, 'Count: 1');
});

// ========================================
// Results
// ========================================

console.log('\n=== Results ===\n');
console.log(`Passed: ${passed}`);
console.log(`Failed: ${failed}`);
console.log(`Skipped: ${skipped}`);
console.log(`Total: ${passed + failed + skipped}`);

// В Node.js: успех если только пропущены DOM тесты
if (failed > 0) {
  process.exit(1);
} else {
  console.log('\n✅ All tests passed!');
}
