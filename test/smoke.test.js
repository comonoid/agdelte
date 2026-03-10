/**
 * Agdelte Smoke Tests
 * Verifies that compiled Agda modules and runtime JS load without errors.
 * Run after `npm run build:*` to catch broken imports, syntax errors, etc.
 *
 * Usage: node test/smoke.test.js
 */

import { readdir } from 'fs/promises';
import { join, dirname } from 'path';
import { fileURLToPath } from 'url';

const __dirname = dirname(fileURLToPath(import.meta.url));
const rootDir = join(__dirname, '..');
const buildDir = join(rootDir, '_build');
const runtimeDir = join(rootDir, 'runtime');

let passed = 0;
let failed = 0;
const failures = [];

async function test(name, fn) {
  try {
    await fn();
    console.log(`✓ ${name}`);
    passed++;
  } catch (e) {
    console.log(`✗ ${name}: ${e.message}`);
    failures.push({ name, error: e.message });
    failed++;
  }
}

// ─── Runtime modules ─────────────────────────────────────────────────

console.log('\n=== Runtime modules ===\n');

// Modules that use DOM/Worker APIs at module level — browser-only, skip in Node
const browserOnly = new Set(['reactive-gl.js', 'reactive-auto.js', 'update-worker.js']);

const runtimeModules = [
  'reactive.js',
  'events.js',
  'agda-values.js',
  'reactive-gl.js',
  'reactive-auto.js',
  'worker-pool.js',
  'buffer-registry.js',
  'svg-events.js',
  'update-worker.js',
];

for (const mod of runtimeModules) {
  if (browserOnly.has(mod)) {
    console.log(`– runtime/${mod} skipped (browser-only)`);
    continue;
  }
  await test(`runtime/${mod} loads`, async () => {
    await import(join(runtimeDir, mod));
  });
}

// ─── Compiled Agda modules (_build/) ─────────────────────────────────

console.log('\n=== Compiled Agda modules (_build/) ===\n');

let buildFiles;
try {
  buildFiles = (await readdir(buildDir)).filter(f => f.endsWith('.mjs')).sort();
} catch {
  console.log(`⚠ _build/ not found — skip compiled module tests (run npm run build:* first)`);
  buildFiles = [];
}

if (buildFiles.length > 0) {
  console.log(`Found ${buildFiles.length} compiled modules\n`);

  for (const file of buildFiles) {
    await test(`_build/${file} loads`, async () => {
      await import(join(buildDir, file));
    });
  }
} else {
  console.log('No compiled modules found, skipping.\n');
}

// ─── Results ─────────────────────────────────────────────────────────

console.log(`\n=== Results ===\n`);
console.log(`Passed: ${passed}`);
console.log(`Failed: ${failed}`);
console.log(`Total: ${passed + failed}`);

if (failures.length > 0) {
  console.log('\nFailures:');
  for (const f of failures) {
    console.log(`  ${f.name}: ${f.error}`);
  }
}

console.log('');
process.exit(failed > 0 ? 1 : 0);
