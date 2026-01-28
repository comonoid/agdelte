/**
 * Agdelte Auto-loader
 *
 * Automatically mounts Agdelte apps based on data attributes.
 * Zero JavaScript required in HTML files!
 *
 * Usage:
 *   <div id="app" data-agdelte="Counter"></div>
 *   <script type="module" src="runtime/auto.js"></script>
 *
 * Options via data attributes:
 *   data-agdelte="ModuleName"     - Module to load (required)
 *   data-build-dir="../_build"    - Build directory (default: ../_build)
 *   data-build-cmd="npm run ..."  - Build command for error message
 */

import { mount } from './index.js';

// Find all elements with data-agdelte attribute
const elements = document.querySelectorAll('[data-agdelte]');

for (const container of elements) {
  const moduleName = container.dataset.agdelte;
  if (!moduleName) continue;

  const buildDir = container.dataset.buildDir || '../_build';
  const buildCmd = container.dataset.buildCmd ||
    `npm run build:${moduleName.toLowerCase().replace('demo', '')}`;

  mountAuto(moduleName, container, { buildDir, buildCmd });
}

async function mountAuto(moduleName, container, { buildDir, buildCmd }) {
  const modulePath = `${buildDir}/jAgda.${moduleName}.mjs`;

  try {
    const module = await import(modulePath);
    mount(module.default, container);
    console.log(`Agdelte: ${moduleName} mounted`);
  } catch (e) {
    console.error(`Agdelte: Failed to load ${moduleName}:`, e);
    container.innerHTML = `
      <div class="error">
        <strong>Failed to load ${moduleName}:</strong> ${e.message}
        <pre>${e.stack}</pre>
        <p style="margin-top:1rem">Run: <code>${buildCmd}</code></p>
      </div>
    `;
  }
}
