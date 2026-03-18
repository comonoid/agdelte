/**
 * Tests for reactive-gl.js pure math functions (no WebGL/DOM required)
 */

import { _test as gl } from '../runtime/reactive-gl.js';

let passed = 0, failed = 0;

function test(name, fn) {
  try { fn(); console.log(`\u2713 ${name}`); passed++; }
  catch (e) { console.log(`\u2717 ${name}: ${e.message}`); failed++; }
}

function assert(cond, msg) { if (!cond) throw new Error(msg || 'assertion failed'); }
function near(a, b, eps = 1e-5) { return Math.abs(a - b) < eps; }

function assertMat4Near(a, b, eps = 1e-5) {
  for (let i = 0; i < 16; i++) {
    if (!near(a[i], b[i], eps)) throw new Error(`mat4[${i}]: ${a[i]} != ${b[i]}`);
  }
}

function assertVec3Near(a, b, eps = 1e-5) {
  if (!near(a.x, b.x, eps) || !near(a.y, b.y, eps) || !near(a.z, b.z, eps))
    throw new Error(`vec3 (${a.x},${a.y},${a.z}) != (${b.x},${b.y},${b.z})`);
}

// --- mat4 ---

console.log('\n=== GL Math Tests ===\n');

test('mat4Identity is identity', () => {
  const m = gl.mat4Identity();
  assert(m[0] === 1 && m[5] === 1 && m[10] === 1 && m[15] === 1);
  assert(m[1] === 0 && m[4] === 0);
});

test('mat4Multiply identity * identity = identity', () => {
  const I = gl.mat4Identity();
  assertMat4Near(gl.mat4Multiply(I, I), I);
});

test('mat4Invert of identity is identity', () => {
  const I = gl.mat4Identity();
  assertMat4Near(gl.mat4Invert(I), I);
});

test('mat4Invert M * M^-1 = I', () => {
  const m = gl.mat4Perspective(Math.PI / 4, 1.5, 0.1, 100);
  const inv = gl.mat4Invert(m);
  assert(inv !== null);
  assertMat4Near(gl.mat4Multiply(m, inv), gl.mat4Identity(), 1e-4);
});

test('mat4Invert returns null for singular matrix', () => {
  const m = new Float32Array(16); // all zeros
  assert(gl.mat4Invert(m) === null);
});

test('mat4Perspective produces correct aspect ratio', () => {
  const m = gl.mat4Perspective(Math.PI / 2, 2.0, 0.1, 100);
  // m[0] = f/aspect, m[5] = f, where f = 1/tan(fov/2) = 1
  assert(near(m[5], 1.0), 'f should be 1.0 for fov=pi/2');
  assert(near(m[0], 0.5), 'f/aspect should be 0.5');
});

test('mat4Ortho is invertible', () => {
  const m = gl.mat4Ortho(10, 1.5, 0.1, 100);
  const inv = gl.mat4Invert(m);
  assert(inv !== null);
  assertMat4Near(gl.mat4Multiply(m, inv), gl.mat4Identity(), 1e-4);
});

test('mat4LookAt eye at origin looking at +Z', () => {
  const eye = { x: 0, y: 0, z: 0 };
  const target = { x: 0, y: 0, z: -1 };
  const up = { x: 0, y: 1, z: 0 };
  const m = gl.mat4LookAt(eye, target, up);
  // Should be identity (camera at origin looking down -Z is default GL convention)
  assertMat4Near(m, gl.mat4Identity(), 1e-5);
});

test('mat4FromTRS identity transform', () => {
  const pos = { x: 0, y: 0, z: 0 };
  const rot = { x: 0, y: 0, z: 0, w: 1 };
  const scale = { x: 1, y: 1, z: 1 };
  assertMat4Near(gl.mat4FromTRS(pos, rot, scale), gl.mat4Identity());
});

test('mat4FromTRS translation only', () => {
  const pos = { x: 3, y: 4, z: 5 };
  const rot = { x: 0, y: 0, z: 0, w: 1 };
  const scale = { x: 1, y: 1, z: 1 };
  const m = gl.mat4FromTRS(pos, rot, scale);
  assert(near(m[12], 3) && near(m[13], 4) && near(m[14], 5));
});

// --- ray intersections ---

test('raySphere hit', () => {
  const ray = { origin: { x: 0, y: 0, z: -5 }, dir: { x: 0, y: 0, z: 1 } };
  const t = gl.raySphere(ray, { x: 0, y: 0, z: 0 }, 1);
  assert(t !== null && near(t, 4.0));
});

test('raySphere miss', () => {
  const ray = { origin: { x: 0, y: 5, z: -5 }, dir: { x: 0, y: 0, z: 1 } };
  assert(gl.raySphere(ray, { x: 0, y: 0, z: 0 }, 1) === null);
});

test('raySphere ray inside sphere', () => {
  const ray = { origin: { x: 0, y: 0, z: 0 }, dir: { x: 0, y: 0, z: 1 } };
  const t = gl.raySphere(ray, { x: 0, y: 0, z: 0 }, 1);
  assert(t !== null && near(t, 1.0));
});

test('rayAABB hit', () => {
  const ray = { origin: { x: 0, y: 0, z: -5 }, dir: { x: 0, y: 0, z: 1 } };
  const t = gl.rayAABB(ray, 1, 1, 1);
  assert(t !== null && near(t, 4.0));
});

test('rayAABB miss', () => {
  const ray = { origin: { x: 5, y: 5, z: -5 }, dir: { x: 0, y: 0, z: 1 } };
  assert(gl.rayAABB(ray, 1, 1, 1) === null);
});

test('rayPlane hit', () => {
  const ray = { origin: { x: 0, y: 5, z: 0 }, dir: { x: 0, y: -1, z: 0 } };
  const t = gl.rayPlane(ray);
  assert(t !== null && near(t, 5.0));
});

test('rayPlane parallel miss', () => {
  const ray = { origin: { x: 0, y: 5, z: 0 }, dir: { x: 1, y: 0, z: 0 } };
  assert(gl.rayPlane(ray) === null);
});

test('rayAt computes correct point', () => {
  const ray = { origin: { x: 1, y: 2, z: 3 }, dir: { x: 0, y: 0, z: 1 } };
  assertVec3Near(gl.rayAt(ray, 5), { x: 1, y: 2, z: 8 });
});

test('rayToLocal with identity is passthrough', () => {
  const ray = { origin: { x: 1, y: 2, z: 3 }, dir: { x: 0, y: 0, z: 1 } };
  const local = gl.rayToLocal(ray, gl.mat4Identity());
  assert(local !== null);
  assertVec3Near(local.origin, ray.origin);
  assertVec3Near(local.dir, ray.dir);
});

test('unprojectPoint center of screen at near plane', () => {
  const proj = gl.mat4Perspective(Math.PI / 2, 1.0, 1.0, 100);
  const view = gl.mat4Identity();
  const p = gl.unprojectPoint(0, 0, -1, proj, view);
  assert(p !== null);
  // Center of screen at near plane should be (0, 0, -1) for identity view
  assert(near(p.x, 0) && near(p.y, 0) && near(p.z, -1, 0.01));
});

// --- degenerate inputs ---

test('mat4LookAt with parallel up vector does not produce NaN', () => {
  // Looking straight up with up = (0,1,0) — up is parallel to view direction
  const eye = { x: 0, y: 0, z: 0 };
  const target = { x: 0, y: 1, z: 0 };
  const up = { x: 0, y: 1, z: 0 };
  const m = gl.mat4LookAt(eye, target, up);
  for (let i = 0; i < 16; i++) {
    assert(!Number.isNaN(m[i]), `mat4LookAt[${i}] is NaN`);
    assert(Number.isFinite(m[i]), `mat4LookAt[${i}] is Infinity`);
  }
});

test('slerpQuat with dot > 1.0 (nearly identical quaternions)', () => {
  // Identical quaternions — dot product is exactly 1.0 (or >1 with float noise)
  const q = { x: 0, y: 0, z: 0, w: 1 };
  const r = gl.slerpQuat(q, q, 0.5);
  assert(!Number.isNaN(r.x) && !Number.isNaN(r.y) && !Number.isNaN(r.z) && !Number.isNaN(r.w),
    'slerpQuat produced NaN for identical quaternions');
  assert(near(r.w, 1.0) && near(r.x, 0) && near(r.y, 0) && near(r.z, 0),
    'slerpQuat should return identity for identical inputs');
});

test('slerpQuat with dot slightly above 1.0 due to float noise', () => {
  // Quaternions that would produce dot > 1.0 with floating point
  const q = { x: 0, y: 0, z: 0, w: 1 };
  const q2 = { x: 1e-16, y: 0, z: 0, w: 1 };
  const r = gl.slerpQuat(q, q2, 0.5);
  assert(!Number.isNaN(r.x) && !Number.isNaN(r.w), 'slerpQuat produced NaN with near-unit dot');
});

test('tickSingleAnimation with durationMs = 0', () => {
  const binding = {
    type: 'transform',
    animation: {
      startTime: 100,
      durationMs: 0,
      easingFn: t => t,
      from: { pos: { x: 0, y: 0, z: 0 }, rot: { x: 0, y: 0, z: 0, w: 1 }, scale: { x: 1, y: 1, z: 1 } },
      to:   { pos: { x: 5, y: 5, z: 5 }, rot: { x: 0, y: 0, z: 0, w: 1 }, scale: { x: 2, y: 2, z: 2 } },
    },
  };
  const result = gl.tickSingleAnimation(binding, 100);
  assert(result.done === true, 'durationMs=0 should be immediately done');
  assert(near(result.value.pos.x, 5), 'durationMs=0 should snap to target');
  assert(near(result.value.scale.x, 2), 'durationMs=0 should snap scale to target');
});

test('mat4Invert with singular matrix returns null, not NaN', () => {
  // All-zeros matrix (singular)
  const m = new Float32Array(16);
  const inv = gl.mat4Invert(m);
  assert(inv === null, 'singular all-zeros matrix should return null');
  // Matrix with duplicate rows (singular)
  const m2 = new Float32Array([
    1, 0, 0, 0,
    1, 0, 0, 0,
    0, 0, 1, 0,
    0, 0, 0, 1,
  ]);
  const inv2 = gl.mat4Invert(m2);
  if (inv2 !== null) {
    for (let i = 0; i < 16; i++) {
      assert(!Number.isNaN(inv2[i]), `singular mat4Invert[${i}] is NaN`);
    }
  }
});

test('unprojectPoint with w = 0 (degenerate projection)', () => {
  // Use a zero projection matrix — inversion should fail or w=0 should return null
  const zeroProj = new Float32Array(16);
  const view = gl.mat4Identity();
  const p = gl.unprojectPoint(0, 0, 0, zeroProj, view);
  assert(p === null, 'unprojectPoint with zero projection should return null');
});

// --- results ---

console.log(`\n=== Results ===\n\nPassed: ${passed}\nFailed: ${failed}\nTotal: ${passed + failed}\n`);
if (failed > 0) process.exit(1);
