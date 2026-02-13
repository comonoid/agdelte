/**
 * SVG Event Utilities
 * Coordinate conversion and gesture handling for SVG elements
 */

/**
 * Convert screen coordinates to SVG coordinates
 * @param {SVGSVGElement} svg - The root SVG element
 * @param {number} clientX - Screen X coordinate
 * @param {number} clientY - Screen Y coordinate
 * @returns {{ x: number, y: number }} - SVG coordinates
 */
export function screenToSvg(svg, clientX, clientY) {
  const ctm = svg.getScreenCTM();
  if (!ctm) return null;
  const pt = svg.createSVGPoint();
  pt.x = clientX;
  pt.y = clientY;
  const svgPt = pt.matrixTransform(ctm.inverse());
  return { x: svgPt.x, y: svgPt.y };
}

/**
 * Convert SVG coordinates to screen coordinates
 * @param {SVGSVGElement} svg - The root SVG element
 * @param {number} svgX - SVG X coordinate
 * @param {number} svgY - SVG Y coordinate
 * @returns {{ x: number, y: number }} - Screen coordinates
 */
export function svgToScreen(svg, svgX, svgY) {
  const ctm = svg.getScreenCTM();
  if (!ctm) return null;
  const pt = svg.createSVGPoint();
  pt.x = svgX;
  pt.y = svgY;
  const screenPt = pt.matrixTransform(ctm);
  return { x: screenPt.x, y: screenPt.y };
}

/**
 * Find the nearest parent SVG element
 * @param {Element} el - Starting element
 * @returns {SVGSVGElement|null}
 */
export function findSvgRoot(el) {
  let current = el;
  while (current) {
    if (current.tagName === 'svg') return current;
    current = current.parentElement;
  }
  return null;
}

/**
 * Extract SVG coordinates from a mouse/pointer event
 * @param {MouseEvent|PointerEvent} event
 * @returns {{ x: number, y: number }|null}
 */
export function getSvgPoint(event) {
  const svg = findSvgRoot(event.target);
  if (!svg) return null;
  return screenToSvg(svg, event.clientX, event.clientY);
}

/**
 * Create a drag handler for SVG elements
 * Returns cleanup function
 * @param {Element} target - Element to attach drag to
 * @param {Object} callbacks - { onStart, onMove, onEnd }
 * @returns {Function} - Cleanup function
 */
export function createSvgDrag(target, callbacks) {
  const svg = findSvgRoot(target);
  if (!svg) return () => {};

  let isDragging = false;
  let startPoint = null;

  const onPointerDown = (e) => {
    const pt = screenToSvg(svg, e.clientX, e.clientY);
    if (!pt) return;
    isDragging = true;
    startPoint = pt;
    target.setPointerCapture(e.pointerId);
    if (callbacks.onStart) {
      callbacks.onStart(startPoint, e);
    }
  };

  const onPointerMove = (e) => {
    if (!isDragging) return;
    const current = screenToSvg(svg, e.clientX, e.clientY);
    if (!current || !startPoint) return;
    const delta = {
      x: current.x - startPoint.x,
      y: current.y - startPoint.y
    };
    if (callbacks.onMove) {
      callbacks.onMove(current, delta, e);
    }
  };

  const onPointerUp = (e) => {
    if (!isDragging) return;
    isDragging = false;
    const end = screenToSvg(svg, e.clientX, e.clientY);
    target.releasePointerCapture(e.pointerId);
    if (callbacks.onEnd) {
      callbacks.onEnd(end, e);
    }
  };

  target.addEventListener('pointerdown', onPointerDown);
  target.addEventListener('pointermove', onPointerMove);
  target.addEventListener('pointerup', onPointerUp);
  target.addEventListener('pointercancel', onPointerUp);

  return () => {
    target.removeEventListener('pointerdown', onPointerDown);
    target.removeEventListener('pointermove', onPointerMove);
    target.removeEventListener('pointerup', onPointerUp);
    target.removeEventListener('pointercancel', onPointerUp);
  };
}

/**
 * Create a pinch/zoom handler for SVG elements
 * @param {SVGSVGElement} svg - SVG element
 * @param {Object} callbacks - { onPinch: (scale, center) => void }
 * @returns {Function} - Cleanup function
 */
export function createSvgPinch(svg, callbacks) {
  let initialDistance = null;
  let initialCenter = null;
  const activePointers = new Map();

  const getDistance = () => {
    const pts = Array.from(activePointers.values());
    if (pts.length < 2) return null;
    const dx = pts[1].x - pts[0].x;
    const dy = pts[1].y - pts[0].y;
    return Math.sqrt(dx * dx + dy * dy);
  };

  const getCenter = () => {
    const pts = Array.from(activePointers.values());
    if (pts.length < 2) return null;
    return {
      x: (pts[0].x + pts[1].x) / 2,
      y: (pts[0].y + pts[1].y) / 2
    };
  };

  const onPointerDown = (e) => {
    const pt = screenToSvg(svg, e.clientX, e.clientY);
    if (!pt) return;
    activePointers.set(e.pointerId, pt);
    if (activePointers.size === 2) {
      initialDistance = getDistance();
      initialCenter = getCenter();
    }
  };

  const onPointerMove = (e) => {
    if (!activePointers.has(e.pointerId)) return;
    const pt = screenToSvg(svg, e.clientX, e.clientY);
    if (!pt) return;
    activePointers.set(e.pointerId, pt);

    if (activePointers.size === 2 && initialDistance > 1e-6) {
      const currentDistance = getDistance();
      if (currentDistance === null) return;
      const scale = currentDistance / initialDistance;
      const center = getCenter();
      if (callbacks.onPinch) {
        callbacks.onPinch(scale, center);
      }
    }
  };

  const onPointerUp = (e) => {
    activePointers.delete(e.pointerId);
    if (activePointers.size < 2) {
      initialDistance = null;
      initialCenter = null;
    }
  };

  svg.addEventListener('pointerdown', onPointerDown);
  svg.addEventListener('pointermove', onPointerMove);
  svg.addEventListener('pointerup', onPointerUp);
  svg.addEventListener('pointercancel', onPointerUp);

  return () => {
    svg.removeEventListener('pointerdown', onPointerDown);
    svg.removeEventListener('pointermove', onPointerMove);
    svg.removeEventListener('pointerup', onPointerUp);
    svg.removeEventListener('pointercancel', onPointerUp);
  };
}
