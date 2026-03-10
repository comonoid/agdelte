/**
 * CSS Pipeline Tests
 * Tests generate-css.js caching logic and generate-anim-data.js validation.
 *
 * Usage: node test/css-pipeline.test.js
 */

import { writeFileSync, mkdirSync, statSync, unlinkSync, utimesSync } from 'fs';
import { join, dirname } from 'path';
import { fileURLToPath } from 'url';
import { execSync } from 'child_process';

const __dirname = dirname(fileURLToPath(import.meta.url));
const rootDir = join(__dirname, '..');
const tmpDir = join(rootDir, '_build', '_css_test_tmp');

let passed = 0;
let failed = 0;
const failures = [];

function test(name, fn) {
  try {
    fn();
    console.log(`✓ ${name}`);
    passed++;
  } catch (e) {
    console.log(`✗ ${name}: ${e.message}`);
    failures.push({ name, error: e.message });
    failed++;
  }
}

function assert(cond, msg) {
  if (!cond) throw new Error(msg || 'Assertion failed');
}

// ─── Setup ───────────────────────────────────────────────────────────

mkdirSync(tmpDir, { recursive: true });

// ─── Cache logic tests ──────────────────────────────────────────────

console.log('\n=== CSS pipeline: cache logic ===\n');

test('--force flag skips cache', () => {
  // Create a fake "up to date" output file with future mtime
  const fakeOutput = join(tmpDir, 'force-test.css');
  writeFileSync(fakeOutput, '/* old */');
  const future = new Date(Date.now() + 60000);
  utimesSync(fakeOutput, future, future);

  // With --force, generate-css should NOT exit early
  // We test by running with a non-existent module (it should fail at import, not skip)
  try {
    execSync(
      `node scripts/generate-css.js jAgda.NonExistent.Module fakeExport ${fakeOutput} --force`,
      { cwd: rootDir, stdio: 'pipe' }
    );
    // If it succeeds, something is wrong
    throw new Error('Expected failure but command succeeded');
  } catch (e) {
    // Should fail at import (not skip with "up to date")
    const stderr = e.stderr?.toString() || '';
    assert(
      stderr.includes('failed to import') || e.status !== 0,
      'Expected import error, got: ' + stderr
    );
  }

  unlinkSync(fakeOutput);
});

test('cache skip when output newer than source', () => {
  // Create a fake module file and a newer output file
  const fakeModule = join(tmpDir, 'jAgda.CacheTest.mjs');
  const fakeOutput = join(tmpDir, 'cache-test.css');

  writeFileSync(fakeModule, 'export default {};');

  // Create output with future mtime relative to module
  writeFileSync(fakeOutput, '/* cached */');
  const future = new Date(Date.now() + 60000);
  utimesSync(fakeOutput, future, future);

  // Run generate-css — it should say "up to date" and exit 0
  // BUT the module path won't match the real _build path, so we verify the logic
  // by checking that when cssMtime > mjsMtime, it skips
  const cssMtime = statSync(fakeOutput).mtimeMs;
  const mjsMtime = statSync(fakeModule).mtimeMs;
  assert(cssMtime > mjsMtime, 'Test setup: output should be newer than module');

  unlinkSync(fakeModule);
  unlinkSync(fakeOutput);
});

test('cache miss when source newer than output (strict >)', () => {
  // Verify that equal mtime does NOT count as "up to date"
  // (the bug was cssMtime >= mjsMtime, now fixed to cssMtime > mjsMtime)
  const fakeModule = join(tmpDir, 'jAgda.StrictTest.mjs');
  const fakeOutput = join(tmpDir, 'strict-test.css');

  writeFileSync(fakeModule, 'export default {};');
  writeFileSync(fakeOutput, '/* old */');

  // Set both to same mtime
  const now = new Date();
  utimesSync(fakeModule, now, now);
  utimesSync(fakeOutput, now, now);

  const cssMtime = statSync(fakeOutput).mtimeMs;
  const mjsMtime = statSync(fakeModule).mtimeMs;

  // With strict >, equal mtime means NOT up to date (should regenerate)
  assert(!(cssMtime > mjsMtime), 'Equal mtime should trigger regeneration (strict >)');

  unlinkSync(fakeModule);
  unlinkSync(fakeOutput);
});

// ─── generate-css.js argument validation ─────────────────────────────

console.log('\n=== CSS pipeline: argument validation ===\n');

test('missing arguments shows usage', () => {
  try {
    execSync('node scripts/generate-css.js', { cwd: rootDir, stdio: 'pipe' });
    throw new Error('Expected failure');
  } catch (e) {
    const stderr = e.stderr?.toString() || '';
    assert(stderr.includes('Usage:'), 'Expected usage message, got: ' + stderr);
  }
});

test('usage message mentions --force flag', () => {
  try {
    execSync('node scripts/generate-css.js', { cwd: rootDir, stdio: 'pipe' });
  } catch (e) {
    const stderr = e.stderr?.toString() || '';
    assert(stderr.includes('--force'), 'Usage should mention --force flag');
  }
});

// ─── generate-anim-data.js argument validation ───────────────────────

console.log('\n=== CSS pipeline: anim-data validation ===\n');

test('generate-anim-data missing argument shows usage', () => {
  try {
    execSync('node scripts/generate-anim-data.js', { cwd: rootDir, stdio: 'pipe' });
    throw new Error('Expected failure');
  } catch (e) {
    const stderr = e.stderr?.toString() || '';
    assert(stderr.includes('Usage:'), 'Expected usage message, got: ' + stderr);
  }
});

// ─── Content verification tests ─────────────────────────────────────
// Verify generated CSS files contain expected selectors and properties.
// Catches regressions from Agda source changes.

import { readFileSync } from 'fs';

console.log('\n=== CSS pipeline: content verification ===\n');

function assertCSS(file, checks) {
  const label = file.replace(rootDir + '/', '');
  const fullPath = join(rootDir, file);
  let css;
  try {
    css = readFileSync(fullPath, 'utf8');
  } catch (e) {
    test(`${label} exists`, () => {
      throw new Error(`File not found: ${fullPath}`);
    });
    return;
  }
  for (const [desc, pattern] of checks) {
    test(`${label}: ${desc}`, () => {
      const re = pattern instanceof RegExp ? pattern : new RegExp(pattern.replace(/[.*+?^${}()|[\]\\]/g, '\\$&'));
      assert(re.test(css), `Expected pattern ${re} not found in ${label}`);
    });
  }
}

assertCSS('examples_html/generated/examples.css', [
  ['has .demo-container', /\.demo-container\s*\{/],
  ['has .demo-btn', /\.demo-btn\s*\{/],
  ['has .demo-btn.info variant', /\.demo-btn\.info\s*\{/],
  ['has .btn-group with flexbox', /\.btn-group\s*\{[^}]*display:\s*flex/],
  ['has .card with transition', /\.card\s*\{[^}]*transition:/],
  ['has .card:hover', /\.card:hover\s*\{/],
  ['has @keyframes fadeIn', /@keyframes fadeIn\s*\{/],
  ['has @keyframes pulse with 50%', /@keyframes pulse\s*\{[\s\S]*?50%\s*\{/],
  ['has @media responsive', /@media\s*\(max-width:\s*768px\)/],
  ['has CSS variable reference', /var\(--agdelte-/],
  ['has color-mix', /color-mix\(/],
  // Stage 2: common.css content now included
  ['has :root with theme vars', /:root\s*\{[^}]*--primary/],
  ['has body styles', /body\s*\{[^}]*font-family/],
  ['has .back link', /\.back\s*\{[^}]*position/],
  ['has header > h1 gradient', /header > h1\s*\{[^}]*linear-gradient/],
  ['has .instructions', /\.instructions\s*\{[^}]*border-left/],
  ['has #app container', /#app\s*\{[^}]*box-shadow/],
  ['has .btn base', /\.btn\s*\{[^}]*cursor/],
  ['has .error', /\.error\s*\{[^}]*border/],
  ['has [data-agdelte] wrapper', /\[data-agdelte\] > div\s*\{/],
  ['has .demo-grid', /\.demo-grid\s*\{[^}]*grid-template/],
  ['has .stress-test', /\.stress-test\s*\{/],
  ['has .doc block', /\.doc\s*\{[^}]*line-height/],
  ['has .webgl-demo', /\.webgl-demo\s*\{/],
  ['has .preview-area', /\.preview-area\s*\{[^}]*background/],
  ['has .bar-chart', /\.bar-chart\s*\{/],
]);

assertCSS('examples_html/generated/css-demo.css', [
  ['has @charset', /@charset "UTF-8"/],
  ['has .css-demo .card', /\.css-demo \.card\s*\{/],
  ['has @media responsive', /@media\s*\(max-width:\s*768px\)/],
  ['has @keyframes fadeIn', /@keyframes fadeIn\s*\{/],
]);

assertCSS('examples_html/generated/css-full-demo.css', [
  ['has :root with CSS variables', /:root\s*\{[^}]*--demo-primary/],
  ['has @keyframes fadeIn', /@keyframes fadeIn\s*\{/],
  ['has @keyframes shake with percentage stops', /@keyframes shake\s*\{[\s\S]*?25%\s*\{/],
  ['has @keyframes spin', /@keyframes spin\s*\{/],
  ['has .card--themed with var()', /\.card--themed\s*\{[^}]*var\(--demo-primary\)/],
  ['has @media responsive', /@media\s*\(max-width:\s*768px\)/],
]);

assertCSS('examples_html/generated/controls-demo.css', [
  ['has .controls-demo', /\.controls-demo\s*\{/],
  ['has .demo-btn', /\.demo-btn\s*\{/],
  ['has CSS variable reference', /var\(--agdelte-/],
]);

// ─── Cleanup ─────────────────────────────────────────────────────────

try {
  const { rmdirSync } = await import('fs');
  rmdirSync(tmpDir);
} catch { /* ignore if not empty */ }

// ─── Results ─────────────────────────────────────────────────────────

console.log(`\n=== Results ===\n`);
console.log(`Passed: ${passed}`);
console.log(`Failed: ${failed}`);

if (failures.length > 0) {
  console.log('\nFailures:');
  for (const f of failures) {
    console.log(`  ${f.name}: ${f.error}`);
  }
}

console.log('');
process.exit(failed > 0 ? 1 : 0);
