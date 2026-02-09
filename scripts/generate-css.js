#!/usr/bin/env node

// generate-css.js — Agdelte CSS build tool
//
// Compiles an Agda Stylesheet value to a .css file.
// Uses Agda's .agdai caching - skips generation if CSS is newer than compiled module.
//
// Usage:
//   node scripts/generate-css.js <module> <export> <output> [--hash] [--force]
//
// Arguments:
//   module   Compiled module path relative to _build/
//            e.g. jAgda.MyApp.Styles
//   export   Name of the Stylesheet export in that module
//            e.g. appCSS
//   output   Output .css file path
//            e.g. dist/app.css
//   --hash   Append content hash to filename (app.a1b2c3d4.css)
//   --force  Regenerate even if CSS is up to date
//
// Example:
//   # Compile the Agda module first:
//   agda --js --js-es6 --js-optimize --compile-dir=_build -i src myapp/Styles.agda
//
//   # Then generate the CSS:
//   node scripts/generate-css.js jAgda.MyApp.Styles appCSS dist/app.css
//   node scripts/generate-css.js jAgda.MyApp.Styles appCSS dist/app.css --hash

import { writeFileSync, mkdirSync, statSync, existsSync } from 'fs';
import { createHash } from 'crypto';
import { dirname, basename, extname, join, resolve } from 'path';
import { pathToFileURL } from 'url';

const args = process.argv.slice(2);
const hashFlag = args.includes('--hash');
const forceFlag = args.includes('--force');
const positional = args.filter(a => !a.startsWith('--'));

if (positional.length < 3) {
  console.error('Usage: node scripts/generate-css.js <module> <export> <output> [--hash]');
  console.error('');
  console.error('Example:');
  console.error('  node scripts/generate-css.js jAgda.MyApp.Styles appCSS dist/app.css');
  process.exit(1);
}

const [moduleName, exportName, outputPath] = positional;

// Resolve paths
const buildDir = resolve(process.cwd(), '_build');
const modulePath = join(buildDir, `${moduleName}.mjs`);
const stylesheetPath = join(buildDir, 'jAgda.Agdelte.Css.Stylesheet.mjs');
const outputResolved = resolve(outputPath);

// Check if CSS is up to date (skip if output is newer than compiled module)
if (!forceFlag && existsSync(outputResolved) && existsSync(modulePath)) {
  try {
    const cssMtime = statSync(outputResolved).mtimeMs;
    const mjsMtime = statSync(modulePath).mtimeMs;

    if (cssMtime > mjsMtime) {
      console.log(`${outputPath} (up to date)`);
      process.exit(0);
    }
  } catch (e) {
    // If stat fails, regenerate
  }
}

// Dynamic import of compiled modules
const [stylesheetMod, userMod] = await Promise.all([
  import(pathToFileURL(stylesheetPath).href),
  import(pathToFileURL(modulePath).href),
]);

const renderStylesheet = stylesheetMod.default['renderStylesheet'];
const stylesheet = userMod.default[exportName];

if (!renderStylesheet) {
  console.error(`Error: renderStylesheet not found in ${stylesheetPath}`);
  process.exit(1);
}

if (!stylesheet) {
  console.error(`Error: export "${exportName}" not found in ${modulePath}`);
  console.error('Available exports:', Object.keys(userMod.default).join(', '));
  process.exit(1);
}

// Render
const css = renderStylesheet(stylesheet);

// Determine output filename
let finalPath = outputPath;
if (hashFlag) {
  const hash = createHash('md5').update(css).digest('hex').slice(0, 8);
  const dir = dirname(outputPath);
  const ext = extname(outputPath);
  const base = basename(outputPath, ext);
  finalPath = join(dir, `${base}.${hash}${ext}`);
}

// Ensure output directory exists
mkdirSync(dirname(resolve(finalPath)), { recursive: true });

// Write
writeFileSync(finalPath, css);

const bytes = Buffer.byteLength(css, 'utf8');
console.log(`${finalPath} (${bytes} bytes)`);
