// Shared helper for loading compiled Agda modules from _build/

import { resolve, join } from 'path';
import { pathToFileURL } from 'url';

const buildDir = resolve(process.cwd(), '_build');

/**
 * Load a compiled Agda module by name.
 * @param {string} name - Module name (e.g. 'jAgda.MyApp.Styles')
 * @returns {Promise<any>} The module's default export
 */
export function loadAgdaModule(name) {
  const modulePath = join(buildDir, `${name}.mjs`);
  return import(pathToFileURL(modulePath).href);
}

/**
 * Load a compiled Agda module and return its default export.
 * @param {string} name - Module name
 * @returns {Promise<any>}
 */
export function loadAgdaDefault(name) {
  return loadAgdaModule(name).then(m => m.default);
}

export { buildDir };
