/**
 * Worker Pool — manages reusable Web Workers for parallel task execution.
 *
 * Features:
 * - Reuses workers to avoid creation overhead
 * - Queues tasks when all workers busy
 * - Auto-cleanup after idle timeout (30s)
 * - Cancellable tasks
 */

import { ensureNumber } from './agda-values.js';

const POOL_IDLE_TIMEOUT = 30000; // 30s without tasks → cleanup
const POOL_CHECK_INTERVAL = 5000;

/** Format worker error with details (filename, line, stack) */
export function formatWorkerError(e) {
  const parts = [e.message || 'Worker error'];
  if (e.filename) parts.push(`at ${e.filename}:${e.lineno || '?'}:${e.colno || '?'}`);
  if (e.error?.stack) parts.push(`\nStack: ${e.error.stack}`);
  return parts.join(' ');
}

/**
 * @example
 * const pool = new WorkerPool(4, '/workers/compute.js');
 * const handle = pool.submit(inputData, onResult, onError);
 * handle.cancel(); // Cancel if needed
 */
export class WorkerPool {
  /**
   * @param {number} maxSize - Maximum concurrent workers
   * @param {string} scriptUrl - Worker script URL
   */
  constructor(maxSize, scriptUrl) {
    this.maxSize = maxSize;
    this.scriptUrl = scriptUrl;
    this.idle = [];      // idle Worker instances
    this.active = 0;     // count of active tasks
    this.queue = [];     // pending tasks: { input, onMessage, onError, resolve }
    this.lastUsed = Date.now();
    // Error backoff: tracks consecutive creation failures to prevent rapid
    // create-error-terminate cycles when the worker script is broken.
    this._consecutiveErrors = 0;
    this._backoffUntil = 0;
  }

  /**
   * Submit a task to the pool.
   * @param {*} input - Data to send to worker via postMessage
   * @param {Function} onMessage - Called with MessageEvent on worker response
   * @param {Function} onError - Called with error string on failure
   * @returns {{ cancel: Function }} Handle with cancel() method
   */
  submit(input, onMessage, onError) {
    this.lastUsed = Date.now();
    let activeWorker = null;

    const task = { input, onMessage, onError, cancelled: false };

    const tryRun = () => {
      if (task.cancelled) return;

      // Backoff check: if recent errors caused a backoff, delay this task
      if (Date.now() < this._backoffUntil) {
        const delay = this._backoffUntil - Date.now();
        setTimeout(() => {
          if (!task.cancelled) tryRun();
        }, delay);
        return;
      }

      if (this.idle.length > 0) {
        activeWorker = this.idle.pop();
      } else if (this.active + this.idle.length < this.maxSize) {
        try {
          activeWorker = new Worker(this.scriptUrl, { type: 'module' });
        } catch (e) {
          this._recordError();
          onError(e.message || 'Failed to create worker');
          return;
        }
      } else {
        // All busy — enqueue
        this.queue.push({ task, tryRun });
        return;
      }

      this.active++;
      activeWorker.onmessage = (e) => {
        if (task.cancelled) return;
        const w = activeWorker;
        activeWorker = null;
        this._consecutiveErrors = 0;  // reset on success
        onMessage(e);
        this.active--;
        this._returnWorker(w);
        this._processQueue();
      };
      activeWorker.onerror = (e) => {
        if (task.cancelled) return;
        const w = activeWorker;
        activeWorker = null;
        this._recordError();
        onError(formatWorkerError(e));
        this.active--;
        // Don't reuse errored worker — terminate it
        try { w.terminate(); } catch(e) { console.debug('worker terminate:', e.message); }
        this._processQueue();
      };
      activeWorker.postMessage(input);
    };

    tryRun();

    return {
      cancel: () => {
        if (task.cancelled) return;
        task.cancelled = true;
        if (activeWorker) {
          this.active = Math.max(0, this.active - 1);
          // Terminate and don't return to pool (task was mid-flight)
          try { activeWorker.terminate(); } catch(e) { console.debug('worker terminate:', e.message); }
          activeWorker = null;
          this._processQueue();
        }
        // Remove from queue if still there
        this.queue = this.queue.filter(q => q.task !== task);
      }
    };
  }

  _recordError() {
    this._consecutiveErrors++;
    // Exponential backoff: 500ms, 1s, 2s, 4s, ... up to 30s
    const backoffMs = Math.min(500 * Math.pow(2, this._consecutiveErrors - 1), 30000);
    this._backoffUntil = Date.now() + backoffMs;
    if (this._consecutiveErrors >= 3) {
      console.warn(`WorkerPool(${this.scriptUrl}): ${this._consecutiveErrors} consecutive errors, backing off ${backoffMs}ms`);
    }
  }

  _returnWorker(w) {
    // Reset handlers before returning to pool
    w.onmessage = null;
    w.onerror = null;
    this.idle.push(w);
    this.lastUsed = Date.now();
  }

  _processQueue() {
    while (this.queue.length > 0 && (this.idle.length > 0 || this.active + this.idle.length < this.maxSize)) {
      const next = this.queue.shift();
      if (!next.task.cancelled) {
        next.tryRun();
      }
    }
  }

  _cleanup() {
    if (this.active === 0 && this.queue.length === 0 &&
        Date.now() - this.lastUsed > POOL_IDLE_TIMEOUT) {
      this.idle.forEach(w => w.terminate());
      this.idle = [];
      this._isEmpty = true;  // Mark for removal from registry
    }
  }

  destroy() {
    this.idle.forEach(w => w.terminate());
    this.idle = [];
    for (const entry of this.queue) {
      if (!entry.task.cancelled) {
        entry.task.cancelled = true;
        try { entry.task.onError('Pool destroyed'); } catch {}
      }
    }
    this.queue = [];
    this._isEmpty = true;
  }
}

// Global pool registry: key = "poolSize:scriptUrl"
const workerPools = new Map();

// Lazy global cleanup timer — only active when pools exist
let globalCleanupTimer = null;

function ensureGlobalCleanup() {
  if (globalCleanupTimer !== null) return;
  globalCleanupTimer = setInterval(() => {
    for (const [key, pool] of workerPools) {
      pool._cleanup();
      if (pool._isEmpty) {
        pool.destroy();
        workerPools.delete(key);
      }
    }
    if (workerPools.size === 0) {
      clearInterval(globalCleanupTimer);
      globalCleanupTimer = null;
    }
  }, POOL_CHECK_INTERVAL * 2);
}

export function getPool(poolSize, scriptUrl) {
  ensureGlobalCleanup();
  const poolSizeNum = ensureNumber(poolSize);
  const key = `${poolSizeNum}:${scriptUrl}`;
  let pool = workerPools.get(key);
  if (!pool || pool._isEmpty) {
    // Pool was cleaned up or doesn't exist — create fresh
    // No need to call destroy() again — _cleanup() already terminated idle workers
    pool = new WorkerPool(poolSizeNum, scriptUrl);
    workerPools.set(key, pool);
  }
  return pool;
}
