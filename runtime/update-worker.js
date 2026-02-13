/**
 * Update Worker — runs Agda update function in a separate thread
 *
 * Why: Heavy model updates can block the main thread, causing UI jank.
 * This worker runs the update function off-thread and posts the new model back.
 *
 * Protocol:
 *   Main → Worker: { type: 'init', modulePath, model }
 *   Main → Worker: { type: 'update', msg, model }
 *   Worker → Main: { type: 'ready' }
 *   Worker → Main: { type: 'result', model }
 *   Worker → Main: { type: 'error', message }
 */

let updateFn = null;
let NodeModule = null;

self.onmessage = async (event) => {
  const { type, modulePath, nodeModulePath, msg, model } = event.data;

  try {
    switch (type) {
      case 'init': {
        // Load the Agda module and extract update function
        const module = await import(modulePath);
        const appRecord = module.default.app;

        // Bug #34 fix: use parameterized path instead of hardcoded
        const nodePath = nodeModulePath || '../_build/jAgda.Agdelte.Reactive.Node.mjs';
        const nodeModuleImport = await import(nodePath);
        NodeModule = nodeModuleImport.default;

        updateFn = NodeModule.ReactiveApp.update(appRecord);
        self.postMessage({ type: 'ready' });
        break;
      }

      case 'update': {
        if (!updateFn) {
          throw new Error('Worker not initialized. Call init first.');
        }

        // Run the update function
        const newModel = updateFn(msg)(model);
        self.postMessage({ type: 'result', model: newModel });
        break;
      }

      default:
        throw new Error(`Unknown message type: ${type}`);
    }
  } catch (error) {
    self.postMessage({ type: 'error', message: error.message });
  }
};
