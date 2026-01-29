/**
 * Agdelte Reactive Auto-loader
 * Automatically mounts ReactiveApp based on data attributes.
 *
 * Usage:
 *   <div id="app" data-agdelte="Counter"></div>
 *   <script type="module" src="runtime/reactive-auto.js"></script>
 */

import { mountReactive } from './reactive.js';

// Find all elements with data-agdelte attribute
const elements = document.querySelectorAll('[data-agdelte]');

for (const container of elements) {
  const moduleName = container.dataset.agdelte;
  if (!moduleName) continue;

  const buildDir = container.dataset.buildDir || '../_build';

  mountReactive(moduleName, container, { buildDir }).catch((e) => {
    console.error(`Failed to mount ${moduleName}:`, e);
  });
}
