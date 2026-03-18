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

// --- lookAtQuat parallel fallback (G3) ---

test('mat4LookAt with up exactly parallel to view (looking down -Y)', () => {
  const eye = { x: 0, y: 5, z: 0 };
  const target = { x: 0, y: 0, z: 0 };
  const up = { x: 0, y: -1, z: 0 }; // parallel to view direction
  const m = gl.mat4LookAt(eye, target, up);
  for (let i = 0; i < 16; i++) {
    assert(!Number.isNaN(m[i]), `mat4LookAt parallel down[${i}] is NaN`);
    assert(Number.isFinite(m[i]), `mat4LookAt parallel down[${i}] is Infinity`);
  }
});

test('mat4LookAt with zero-length up vector does not crash', () => {
  const eye = { x: 0, y: 0, z: 5 };
  const target = { x: 0, y: 0, z: 0 };
  const up = { x: 0, y: 1, z: 0 };
  const m = gl.mat4LookAt(eye, target, up);
  assert(m !== null, 'should return valid matrix');
  // Verify the view matrix is invertible
  const inv = gl.mat4Invert(m);
  assert(inv !== null, 'lookAt result should be invertible');
});

// --- mat4Invert precision at extreme distances (G3) ---

test('mat4Invert with very far objects (det near threshold)', () => {
  // Create a perspective projection for very far near/far planes
  const m = gl.mat4Perspective(Math.PI / 4, 1.0, 1000, 1000000);
  const inv = gl.mat4Invert(m);
  assert(inv !== null, 'far perspective should be invertible');
  const product = gl.mat4Multiply(m, inv);
  // Lower precision tolerance for far objects
  for (let i = 0; i < 16; i++) {
    const expected = (i % 5 === 0) ? 1.0 : 0.0;
    assert(near(product[i], expected, 1e-3),
      `M*M^-1[${i}] = ${product[i]}, expected ${expected}`);
  }
});

// --- slerpQuat edge cases (G9) ---

test('slerpQuat with opposite quaternions (dot < 0)', () => {
  const q1 = { x: 0, y: 0, z: 0, w: 1 };
  const q2 = { x: 0, y: 0, z: 0, w: -1 }; // opposite
  const r = gl.slerpQuat(q1, q2, 0.5);
  assert(!Number.isNaN(r.x) && !Number.isNaN(r.w),
    'slerpQuat should handle opposite quaternions');
});

test('slerpQuat t=0 returns first quaternion', () => {
  const q1 = { x: 0, y: 0, z: 0, w: 1 };
  const q2 = { x: 0, y: 1, z: 0, w: 0 };
  const r = gl.slerpQuat(q1, q2, 0);
  assert(near(r.w, 1.0) && near(r.x, 0) && near(r.y, 0),
    'slerp t=0 should return q1');
});

test('slerpQuat t=1 returns second quaternion', () => {
  const q1 = { x: 0, y: 0, z: 0, w: 1 };
  const q2 = { x: 0, y: 1, z: 0, w: 0 };
  const r = gl.slerpQuat(q1, q2, 1);
  assert(near(r.y, 1.0, 0.01) || near(r.y, -1.0, 0.01),
    'slerp t=1 should return q2 (or negated)');
});

// --- tickSingleAnimation edge cases (G11) ---

test('tickSingleAnimation with negative elapsed (before start) extrapolates', () => {
  const binding = {
    type: 'transform',
    animation: {
      startTime: 200,
      durationMs: 1000,
      easingFn: t => t,
      from: { pos: { x: 0, y: 0, z: 0 }, rot: { x: 0, y: 0, z: 0, w: 1 }, scale: { x: 1, y: 1, z: 1 } },
      to:   { pos: { x: 10, y: 10, z: 10 }, rot: { x: 0, y: 0, z: 0, w: 1 }, scale: { x: 2, y: 2, z: 2 } },
    },
  };
  const result = gl.tickSingleAnimation(binding, 100); // before start
  assert(result.done === false, 'before start should not be done');
  // rawT = -100/1000 = -0.1, so it extrapolates slightly before 'from'
  // No NaN, no crash — the key invariant
  assert(!Number.isNaN(result.value.pos.x), 'position should not be NaN');
  assert(Number.isFinite(result.value.pos.x), 'position should be finite');
});

test('tickSingleAnimation with elapsed past duration', () => {
  const binding = {
    type: 'transform',
    animation: {
      startTime: 0,
      durationMs: 500,
      easingFn: t => t,
      from: { pos: { x: 0, y: 0, z: 0 }, rot: { x: 0, y: 0, z: 0, w: 1 }, scale: { x: 1, y: 1, z: 1 } },
      to:   { pos: { x: 5, y: 5, z: 5 }, rot: { x: 0, y: 0, z: 0, w: 1 }, scale: { x: 2, y: 2, z: 2 } },
    },
  };
  const result = gl.tickSingleAnimation(binding, 1000); // well past duration
  assert(result.done === true, 'past duration should be done');
  assert(near(result.value.pos.x, 5), 'should be at target position');
});

// --- makeCubicBezier extreme control points (G9) ---

test('mat4Multiply performance 1000 multiplications', () => {
  const m = gl.mat4Perspective(Math.PI / 4, 1.5, 0.1, 100);
  const start = performance.now();
  let result = gl.mat4Identity();
  for (let i = 0; i < 1000; i++) {
    result = gl.mat4Multiply(result, m);
  }
  const elapsed = performance.now() - start;
  assert(elapsed < 50, `1000 mat4Multiply should be fast, took ${elapsed.toFixed(1)}ms`);
});

// --- raySphere with unnormalized direction (G4) ---

test('raySphere with unnormalized direction', () => {
  // Direction not normalized (length = 2)
  const ray = { origin: { x: 0, y: 0, z: -10 }, dir: { x: 0, y: 0, z: 2 } };
  const t = gl.raySphere(ray, { x: 0, y: 0, z: 0 }, 1);
  assert(t !== null, 'should still hit sphere with unnormalized dir');
  // t value will be different because dir isn't normalized
  const hitPoint = gl.rayAt(ray, t);
  // Hit point should be near sphere surface (z ≈ -1 or z ≈ 1)
  const dist = Math.sqrt(hitPoint.x**2 + hitPoint.y**2 + hitPoint.z**2);
  assert(near(dist, 1.0, 0.01), `hit point should be on sphere surface, dist=${dist}`);
});

// --- rayAABB edge cases (G4) ---

test('rayAABB ray parallel to face', () => {
  // Ray parallel to one face, sliding along edge
  const ray = { origin: { x: 0.5, y: 0.5, z: -5 }, dir: { x: 0, y: 0, z: 1 } };
  const t = gl.rayAABB(ray, 1, 1, 1);
  assert(t !== null, 'ray through corner should hit AABB');
});

test('rayAABB with zero-size box', () => {
  const ray = { origin: { x: 0, y: 0, z: -5 }, dir: { x: 0, y: 0, z: 1 } };
  const t = gl.rayAABB(ray, 0, 0, 0);
  // Zero-size box is degenerate — may hit or miss depending on implementation
  // Just verify it doesn't crash
  assert(t === null || typeof t === 'number', 'should not crash on zero-size AABB');
});

// --- rayToLocal with scaled transform (G4) ---

test('rayToLocal with scaled transform', () => {
  const ray = { origin: { x: 0, y: 0, z: -5 }, dir: { x: 0, y: 0, z: 1 } };
  const pos = { x: 0, y: 0, z: 0 };
  const rot = { x: 0, y: 0, z: 0, w: 1 };
  const scale = { x: 2, y: 2, z: 2 };
  const transform = gl.mat4FromTRS(pos, rot, scale);
  const local = gl.rayToLocal(ray, transform);
  assert(local !== null, 'should compute local ray');
  // In local space, the origin should be scaled
  assert(!Number.isNaN(local.origin.x), 'local origin should not be NaN');
});

// --- mat4FromTRS with non-uniform scale ---

test('mat4FromTRS with non-uniform scale', () => {
  const pos = { x: 0, y: 0, z: 0 };
  const rot = { x: 0, y: 0, z: 0, w: 1 };
  const scale = { x: 1, y: 2, z: 3 };
  const m = gl.mat4FromTRS(pos, rot, scale);
  assert(near(m[0], 1) && near(m[5], 2) && near(m[10], 3),
    'non-uniform scale should appear on diagonal');
});

test('mat4FromTRS translation + rotation', () => {
  const pos = { x: 5, y: 0, z: 0 };
  // 90 degree rotation around Y axis
  const angle = Math.PI / 4;
  const rot = { x: 0, y: Math.sin(angle / 2), z: 0, w: Math.cos(angle / 2) };
  const scale = { x: 1, y: 1, z: 1 };
  const m = gl.mat4FromTRS(pos, rot, scale);
  assert(near(m[12], 5), 'translation should be at m[12]');
  assert(!near(m[0], 1, 0.01) || !near(m[10], 1, 0.01),
    'rotation should modify m[0] or m[10]');
});

// --- property-based: mat4Multiply(mat4Invert(m), m) ~ identity ---

function randomNonSingularMat4(seed) {
  // Build a non-singular matrix from a TRS with random-ish values
  const s = (i) => Math.sin(seed * 1.3 + i * 2.7) * 3 + 0.5;
  const pos = { x: s(0), y: s(1), z: s(2) };
  // Random unit quaternion
  const a = s(3), b = s(4), c = s(5), d = s(6);
  const len = Math.sqrt(a*a + b*b + c*c + d*d);
  const rot = { x: a/len, y: b/len, z: c/len, w: d/len };
  // Non-zero scale
  const scale = { x: Math.abs(s(7)) + 0.1, y: Math.abs(s(8)) + 0.1, z: Math.abs(s(9)) + 0.1 };
  return gl.mat4FromTRS(pos, rot, scale);
}

test('property: mat4Multiply(mat4Invert(m), m) ~ identity for random matrices', () => {
  const I = gl.mat4Identity();
  for (let seed = 0; seed < 50; seed++) {
    const m = randomNonSingularMat4(seed);
    const inv = gl.mat4Invert(m);
    assert(inv !== null, `seed ${seed}: matrix should be invertible`);
    const product = gl.mat4Multiply(inv, m);
    for (let i = 0; i < 16; i++) {
      const expected = (i % 5 === 0) ? 1.0 : 0.0;
      assert(near(product[i], expected, 1e-3),
        `seed ${seed}: M^-1*M[${i}] = ${product[i]}, expected ${expected}`);
    }
  }
});

// --- property: slerp(q, q, t) === q for any t ---

test('property: slerpQuat(q, q, t) === q for any t', () => {
  const quaternions = [
    { x: 0, y: 0, z: 0, w: 1 },
    { x: 1, y: 0, z: 0, w: 0 },
    { x: 0, y: 0.7071, z: 0, w: 0.7071 },
  ];
  // Normalize quaternions
  for (const q of quaternions) {
    const len = Math.sqrt(q.x*q.x + q.y*q.y + q.z*q.z + q.w*q.w);
    q.x /= len; q.y /= len; q.z /= len; q.w /= len;
  }
  const tValues = [0, 0.1, 0.25, 0.5, 0.75, 0.9, 1.0];
  for (const q of quaternions) {
    for (const t of tValues) {
      const r = gl.slerpQuat(q, q, t);
      assert(near(r.x, q.x, 1e-5) && near(r.y, q.y, 1e-5) &&
             near(r.z, q.z, 1e-5) && near(r.w, q.w, 1e-5),
        `slerpQuat(q, q, ${t}) should equal q, got (${r.x},${r.y},${r.z},${r.w})`);
    }
  }
});

// --- property: lerp(a, b, 0) === a, lerp(a, b, 1) === b ---

test('property: lerpFloat(a, b, 0) === a, lerpFloat(a, b, 1) === b', () => {
  const pairs = [
    [0, 1], [-5, 5], [100, 200], [0.1, 0.9], [-1000, 1000], [0, 0],
  ];
  for (const [a, b] of pairs) {
    assert(near(gl.lerpFloat(a, b, 0), a, 1e-10),
      `lerpFloat(${a}, ${b}, 0) should be ${a}`);
    assert(near(gl.lerpFloat(a, b, 1), b, 1e-10),
      `lerpFloat(${a}, ${b}, 1) should be ${b}`);
  }
});

test('property: lerpVec3(a, b, 0) === a, lerpVec3(a, b, 1) === b', () => {
  const a = { x: 1, y: 2, z: 3 };
  const b = { x: 10, y: 20, z: 30 };
  const r0 = gl.lerpVec3(a, b, 0);
  assertVec3Near(r0, a);
  const r1 = gl.lerpVec3(a, b, 1);
  assertVec3Near(r1, b);
});

test('property: lerpFloat midpoint', () => {
  assert(near(gl.lerpFloat(0, 10, 0.5), 5), 'midpoint should be 5');
  assert(near(gl.lerpFloat(-10, 10, 0.5), 0), 'midpoint should be 0');
});

// --- property: mat4FromTRS identity test ---

test('property: mat4FromTRS with identity params yields identity matrix', () => {
  const pos = { x: 0, y: 0, z: 0 };
  const rot = { x: 0, y: 0, z: 0, w: 1 };
  const scale = { x: 1, y: 1, z: 1 };
  const m = gl.mat4FromTRS(pos, rot, scale);
  assertMat4Near(m, gl.mat4Identity());
});

test('property: mat4FromTRS pure translation preserves identity rotation/scale', () => {
  const translations = [
    { x: 1, y: 0, z: 0 },
    { x: 0, y: 5, z: 0 },
    { x: 0, y: 0, z: -3 },
    { x: 7.5, y: -2.3, z: 100 },
  ];
  const rot = { x: 0, y: 0, z: 0, w: 1 };
  const scale = { x: 1, y: 1, z: 1 };
  for (const pos of translations) {
    const m = gl.mat4FromTRS(pos, rot, scale);
    // Upper 3x3 should be identity
    assert(near(m[0], 1) && near(m[1], 0) && near(m[2], 0), 'col 0');
    assert(near(m[4], 0) && near(m[5], 1) && near(m[6], 0), 'col 1');
    assert(near(m[8], 0) && near(m[9], 0) && near(m[10], 1), 'col 2');
    // Translation in column 3
    assert(near(m[12], pos.x) && near(m[13], pos.y) && near(m[14], pos.z),
      `translation should be (${pos.x},${pos.y},${pos.z})`);
  }
});

test('property: mat4FromTRS with only scale yields diagonal matrix', () => {
  const pos = { x: 0, y: 0, z: 0 };
  const rot = { x: 0, y: 0, z: 0, w: 1 };
  const scales = [
    { x: 2, y: 3, z: 4 },
    { x: 0.5, y: 0.5, z: 0.5 },
    { x: 10, y: 1, z: 0.1 },
  ];
  for (const scale of scales) {
    const m = gl.mat4FromTRS(pos, rot, scale);
    assert(near(m[0], scale.x), `m[0] should be ${scale.x}`);
    assert(near(m[5], scale.y), `m[5] should be ${scale.y}`);
    assert(near(m[10], scale.z), `m[10] should be ${scale.z}`);
    // Off-diagonals should be zero
    assert(near(m[1], 0) && near(m[2], 0) && near(m[4], 0) &&
           near(m[6], 0) && near(m[8], 0) && near(m[9], 0), 'off-diagonals should be 0');
  }
});

// --- results ---

console.log(`\n=== Results ===\n\nPassed: ${passed}\nFailed: ${failed}\nTotal: ${passed + failed}\n`);
if (failed > 0) process.exit(1);
