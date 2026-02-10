/**
 * Buffer Registry — manages large binary buffers outside the Agda model
 *
 * Why: Canvas/WebGL apps need to reference large buffers (images, audio)
 * without passing them through the Agda model on every render.
 *
 * Model stores only lightweight handles (id, version, dimensions).
 * Actual buffer data lives in this registry.
 */

/**
 * Buffer Registry singleton
 */
class BufferRegistry {
  constructor() {
    this.buffers = new Map();  // handle id → { buffer, width?, height?, version }
    this.nextHandle = 1;
  }

  /**
   * Allocate a new buffer
   * @param {number} size - Size in bytes
   * @param {Object} metadata - Optional metadata (width, height, etc.)
   * @returns {number} - Handle id
   */
  allocate(size, metadata = {}) {
    try {
      const buffer = new SharedArrayBuffer(size);
      const id = this.nextHandle++;
      this.buffers.set(id, {
        buffer,
        version: 1,
        ...metadata
      });
      return id;
    } catch (e) {
      console.error('BufferRegistry.allocate failed (COOP/COEP headers required):', e.message);
      return -1;
    }
  }

  /**
   * Allocate a typed buffer for images (RGBA)
   * @param {number} width - Image width
   * @param {number} height - Image height
   * @returns {number} - Handle id
   */
  allocateImage(width, height) {
    const size = width * height * 4;  // RGBA
    return this.allocate(size, { width, height, type: 'image' });
  }

  /**
   * Allocate a typed buffer for audio (Float32)
   * @param {number} sampleCount - Number of samples
   * @param {number} channels - Number of channels (1 = mono, 2 = stereo)
   * @returns {number} - Handle id
   */
  allocateAudio(sampleCount, channels = 1) {
    const size = sampleCount * channels * 4;  // Float32
    return this.allocate(size, { sampleCount, channels, type: 'audio' });
  }

  /**
   * Get buffer by handle id
   * @param {number} id - Handle id
   * @returns {SharedArrayBuffer|null}
   */
  get(id) {
    const entry = this.buffers.get(id);
    return entry ? entry.buffer : null;
  }

  /**
   * Get buffer metadata
   * @param {number} id - Handle id
   * @returns {Object|null} - { buffer, version, width?, height?, ... }
   */
  getEntry(id) {
    return this.buffers.get(id) || null;
  }

  /**
   * Get typed view of buffer
   * @param {number} id - Handle id
   * @param {string} type - 'uint8', 'uint32', 'float32'
   * @returns {TypedArray|null}
   */
  getView(id, type = 'uint8') {
    const buffer = this.get(id);
    if (!buffer) return null;

    switch (type) {
      case 'uint8': return new Uint8Array(buffer);
      case 'uint8clamped': return new Uint8ClampedArray(buffer);
      case 'uint32': return new Uint32Array(buffer);
      case 'int32': return new Int32Array(buffer);
      case 'float32': return new Float32Array(buffer);
      case 'float64': return new Float64Array(buffer);
      default: return new Uint8Array(buffer);
    }
  }

  /**
   * Increment version (signals that buffer content changed)
   * @param {number} id - Handle id
   * @returns {number} - New version number
   */
  touch(id) {
    const entry = this.buffers.get(id);
    if (entry) {
      entry.version++;
      return entry.version;
    }
    return -1;
  }

  /**
   * Get current version
   * @param {number} id - Handle id
   * @returns {number} - Version number or -1 if not found
   */
  version(id) {
    const entry = this.buffers.get(id);
    return entry ? entry.version : -1;
  }

  /**
   * Free buffer
   * @param {number} id - Handle id
   */
  free(id) {
    this.buffers.delete(id);
  }

  /**
   * Get stats for debugging
   * @returns {Object} - { count, totalBytes }
   */
  stats() {
    let totalBytes = 0;
    for (const entry of this.buffers.values()) {
      totalBytes += entry.buffer.byteLength;
    }
    return {
      count: this.buffers.size,
      totalBytes
    };
  }

  /**
   * Clear all buffers
   */
  clear() {
    this.buffers.clear();
    this.nextHandle = 1;
  }
}

// Singleton instance
export const bufferRegistry = new BufferRegistry();

// ─── Helper functions for Agda integration ────────────────────────────────

/**
 * Create a BufferHandle (Scott-encoded record for Agda)
 * @param {number} id - Handle id
 * @param {number} version - Version number
 * @param {number} width - Width (for images)
 * @param {number} height - Height (for images)
 * @returns {Function} - Scott-encoded BufferHandle
 */
export function mkBufferHandle(id, version, width, height) {
  return (cb) => cb.bufferHandle(BigInt(id), BigInt(version), BigInt(width), BigInt(height));
}

/**
 * Extract fields from Scott-encoded BufferHandle
 * @param {Function} handle - Scott-encoded BufferHandle
 * @returns {Object} - { id, version, width, height }
 */
export function extractBufferHandle(handle) {
  return handle({
    bufferHandle: (id, version, width, height) => ({
      id: Number(id),
      version: Number(version),
      width: Number(width),
      height: Number(height)
    })
  });
}

/**
 * Allocate image buffer and return handle
 * @param {number} width
 * @param {number} height
 * @returns {Function} - Scott-encoded BufferHandle
 */
export function allocateImageBuffer(width, height) {
  const id = bufferRegistry.allocateImage(width, height);
  const version = bufferRegistry.version(id);
  return mkBufferHandle(id, version, width, height);
}

/**
 * Update buffer contents via callback and increment version
 * @param {number} id - Handle id
 * @param {Function} updater - (Uint8Array) => void
 * @returns {number} - New version
 */
export function updateBuffer(id, updater) {
  const view = bufferRegistry.getView(id, 'uint8');
  if (view) {
    updater(view);
    return bufferRegistry.touch(id);
  }
  return -1;
}

/**
 * Copy ImageData into buffer
 * @param {number} id - Handle id
 * @param {ImageData} imageData
 * @returns {number} - New version
 */
export function copyImageData(id, imageData) {
  const view = bufferRegistry.getView(id, 'uint8clamped');
  if (view && imageData.data.length === view.length) {
    view.set(imageData.data);
    return bufferRegistry.touch(id);
  }
  return -1;
}

/**
 * Get buffer as ImageData (for canvas)
 * @param {number} id - Handle id
 * @returns {ImageData|null}
 */
export function getImageData(id) {
  const entry = bufferRegistry.getEntry(id);
  if (entry && entry.type === 'image') {
    const view = new Uint8ClampedArray(entry.buffer);
    return new ImageData(view, entry.width, entry.height);
  }
  return null;
}

// Export for testing
export { BufferRegistry };
