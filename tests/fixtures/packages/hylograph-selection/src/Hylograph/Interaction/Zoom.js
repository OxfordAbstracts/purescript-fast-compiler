// Native Zoom implementation using Pointer Events
// No D3 dependency - uses vendored transform math
//
// ZoomTransform class and math adapted from d3-zoom
// Copyright 2010-2021 Mike Bostock
// ISC License: https://github.com/d3/d3-zoom/blob/main/LICENSE

// =============================================================================
// ZoomTransform - vendored from d3-zoom
// =============================================================================

/**
 * Represents a 2D affine transform: translate(x, y) scale(k)
 * Matrix form: [k 0 x; 0 k y; 0 0 1]
 */
class ZoomTransform {
  constructor(k, x, y) {
    this.k = k;  // scale
    this.x = x;  // translate x
    this.y = y;  // translate y
  }

  /**
   * Returns a new transform scaled by k
   */
  scale(k) {
    return k === 1 ? this : new ZoomTransform(this.k * k, this.x, this.y);
  }

  /**
   * Returns a new transform translated by (x, y) in local coordinates
   */
  translate(x, y) {
    return x === 0 && y === 0 ? this
      : new ZoomTransform(this.k, this.x + this.k * x, this.y + this.k * y);
  }

  /**
   * Apply transform to a point [x, y] -> [x', y']
   */
  apply(point) {
    return [point[0] * this.k + this.x, point[1] * this.k + this.y];
  }

  /**
   * Apply inverse transform to get original coordinates
   */
  applyX(x) {
    return x * this.k + this.x;
  }

  applyY(y) {
    return y * this.k + this.y;
  }

  /**
   * Invert: given transformed point, return original point
   */
  invert(point) {
    return [(point[0] - this.x) / this.k, (point[1] - this.y) / this.k];
  }

  invertX(x) {
    return (x - this.x) / this.k;
  }

  invertY(y) {
    return (y - this.y) / this.k;
  }

  /**
   * Rescale a scale's domain according to this transform
   */
  rescaleX(x) {
    return x.copy().domain(x.range().map(this.invertX, this).map(x.invert, x));
  }

  rescaleY(y) {
    return y.copy().domain(y.range().map(this.invertY, this).map(y.invert, y));
  }

  toString() {
    return `translate(${this.x},${this.y}) scale(${this.k})`;
  }
}

const identity = new ZoomTransform(1, 0, 0);

// =============================================================================
// Zoom Math Helpers
// =============================================================================

/**
 * Constrain transform within bounds
 * @param {ZoomTransform} transform - Current transform
 * @param {Array} extent - [[x0, y0], [x1, y1]] viewport bounds
 * @param {Array} translateExtent - [[x0, y0], [x1, y1]] pan limits (content bounds)
 * @returns {ZoomTransform} Constrained transform
 */
function constrain(transform, extent, translateExtent) {
  // Compute content bounds in screen coordinates
  const dx0 = transform.invertX(extent[0][0]) - translateExtent[0][0];
  const dx1 = transform.invertX(extent[1][0]) - translateExtent[1][0];
  const dy0 = transform.invertY(extent[0][1]) - translateExtent[0][1];
  const dy1 = transform.invertY(extent[1][1]) - translateExtent[1][1];

  let x = transform.x;
  let y = transform.y;

  // Constrain horizontal
  if (dx1 > dx0) {
    x += (dx0 + dx1) / 2 * transform.k;
  } else if (dx0 < 0) {
    x -= dx0 * transform.k;
  } else if (dx1 > 0) {
    x -= dx1 * transform.k;
  }

  // Constrain vertical
  if (dy1 > dy0) {
    y += (dy0 + dy1) / 2 * transform.k;
  } else if (dy0 < 0) {
    y -= dy0 * transform.k;
  } else if (dy1 > 0) {
    y -= dy1 * transform.k;
  }

  return x === transform.x && y === transform.y ? transform
    : new ZoomTransform(transform.k, x, y);
}

/**
 * Zoom around a point, keeping that point visually fixed
 * @param {ZoomTransform} transform - Current transform
 * @param {Array} point - [x, y] screen coordinates to zoom around
 * @param {number} newK - New scale factor
 * @returns {ZoomTransform} New transform
 */
function zoomAround(transform, point, newK) {
  // Get the point in content coordinates
  const p = transform.invert(point);
  // Scale
  const t = transform.scale(newK / transform.k);
  // Translate so the content point p appears at screen point
  return new ZoomTransform(
    t.k,
    point[0] - p[0] * t.k,
    point[1] - p[1] * t.k
  );
}

// =============================================================================
// Native Zoom Implementation
// =============================================================================

/**
 * Attach native zoom behavior to an element
 *
 * @param {Element} element - Container element (SVG) that receives events
 * @param {Object} config - Zoom configuration
 *   - scaleMin: minimum scale (default 0.1)
 *   - scaleMax: maximum scale (default 10)
 *   - targetSelector: CSS selector for element to transform
 *   - initialTransform: optional {k, x, y} to start with
 *   - translateExtent: optional [[x0,y0],[x1,y1]] pan limits
 *   - onZoom: optional callback (transform -> Effect Unit)
 * @returns {Object} ZoomHandle with methods
 */
export function attachNativeZoom_(element) {
  return config => () => {
    const scaleMin = config.scaleMin || 0.1;
    const scaleMax = config.scaleMax || 10;
    const targetSelector = config.targetSelector;

    // Current transform state
    let transform = config.initialTransform
      ? new ZoomTransform(
          config.initialTransform.k,
          config.initialTransform.x,
          config.initialTransform.y
        )
      : identity;

    // Viewport extent - lazy initialized
    let extent = null;
    function getExtent() {
      if (!extent) {
        const rect = element.getBoundingClientRect();
        extent = [[0, 0], [rect.width, rect.height]];
      }
      return extent;
    }

    // =============================================================================
    // SVG Coordinate Conversion
    // =============================================================================
    // SVG viewBox can scale coordinates differently from screen pixels.
    // We need to convert screen coordinates to SVG coordinates for proper
    // zoom point calculation and pan delta computation.

    /**
     * Convert screen coordinates to SVG coordinates
     * @param {number} clientX - Screen X coordinate
     * @param {number} clientY - Screen Y coordinate
     * @returns {[number, number]} SVG coordinates
     */
    function toSVGCoords(clientX, clientY) {
      const svg = element.ownerSVGElement || element;
      if (svg.createSVGPoint) {
        const pt = svg.createSVGPoint();
        pt.x = clientX;
        pt.y = clientY;
        const ctm = svg.getScreenCTM();
        if (ctm) {
          const inv = ctm.inverse();
          const svgPt = pt.matrixTransform(inv);
          return [svgPt.x, svgPt.y];
        }
      }
      // Fallback: use bounding rect offset (doesn't handle viewBox scaling)
      const rect = element.getBoundingClientRect();
      return [clientX - rect.left, clientY - rect.top];
    }

    /**
     * Convert screen delta to SVG delta
     * This accounts for viewBox scaling when computing pan distances.
     * @param {number} screenDx - Screen X delta
     * @param {number} screenDy - Screen Y delta
     * @returns {[number, number]} SVG coordinate deltas
     */
    function toSVGDelta(screenDx, screenDy) {
      const svg = element.ownerSVGElement || element;
      if (svg.getScreenCTM) {
        const ctm = svg.getScreenCTM();
        if (ctm) {
          // The CTM includes translation, but we only want the scale part for deltas
          // For uniform scale (which SVG viewBox gives us), we can use ctm.a (x scale)
          // Delta in SVG space = delta in screen space / scale
          const scale = ctm.a; // Assumes uniform scaling (common for SVG viewBox)
          return [screenDx / scale, screenDy / scale];
        }
      }
      // Fallback: 1:1 mapping
      return [screenDx, screenDy];
    }

    // Translate extent (pan limits) - null means infinite
    let translateExtent = config.translateExtent || null;
    const infiniteExtent = [[-Infinity, -Infinity], [Infinity, Infinity]];

    // Apply transform to target element
    function applyTransform() {
      const target = element.querySelector(targetSelector);
      if (target) {
        target.setAttribute('transform', transform.toString());
      }
      // Store transform on element for compatibility with getZoomTransform_
      // This mimics D3's __zoom property
      element.__zoom = transform;

      // Call PureScript callback if provided
      if (config.onZoom) {
        config.onZoom({ k: transform.k, x: transform.x, y: transform.y })();
      }
    }

    // Constrain and apply new transform
    function setTransform(newTransform) {
      // Clamp scale
      const k = Math.max(scaleMin, Math.min(scaleMax, newTransform.k));
      newTransform = new ZoomTransform(k, newTransform.x, newTransform.y);

      // Apply translate constraints if configured
      if (translateExtent) {
        newTransform = constrain(newTransform, getExtent(), translateExtent);
      }

      transform = newTransform;
      applyTransform();
    }

    // === Wheel Zoom ===
    function handleWheel(event) {
      event.preventDefault();

      // Get pointer position in SVG coordinates
      // This accounts for viewBox scaling
      const point = toSVGCoords(event.clientX, event.clientY);

      // Compute zoom factor from deltaY
      // Negative deltaY = zoom in, positive = zoom out
      // Use smaller factor for smoother zooming
      const factor = Math.pow(2, -event.deltaY * 0.002);

      // Compute new scale and clamp BEFORE calculating transform
      // This ensures the translation is calculated for the actual clamped scale
      const newK = Math.max(scaleMin, Math.min(scaleMax, transform.k * factor));

      // Don't update if we're already at the limit (with tolerance for floating point)
      if (Math.abs(newK - transform.k) < 0.001) return;

      const newTransform = zoomAround(transform, point, newK);
      setTransform(newTransform);
    }

    // === Pointer Pan ===
    let isPanning = false;
    let panStart = null;
    let transformAtPanStart = null;

    function handlePointerDown(event) {
      // Only pan on primary button
      if (event.button !== 0) return;

      // Only start pan if clicking on the SVG itself or a background element
      // Don't capture clicks on interactive elements (circles, etc.) - let them handle their own clicks
      const target = event.target;
      const isPanTarget = target === element ||  // SVG element itself
                          target.tagName === 'svg' ||
                          target.classList.contains('zoom-background') ||
                          target.classList.contains('zoom-group');

      if (!isPanTarget) {
        return;  // Let the event propagate to click handlers
      }

      isPanning = true;
      panStart = [event.clientX, event.clientY];
      transformAtPanStart = transform;

      element.setPointerCapture(event.pointerId);
      element.style.cursor = 'grabbing';
    }

    function handlePointerMove(event) {
      if (!isPanning) return;

      // Calculate screen delta
      const screenDx = event.clientX - panStart[0];
      const screenDy = event.clientY - panStart[1];

      // Convert to SVG coordinate delta (accounts for viewBox scaling)
      const [dx, dy] = toSVGDelta(screenDx, screenDy);

      const newTransform = new ZoomTransform(
        transformAtPanStart.k,
        transformAtPanStart.x + dx,
        transformAtPanStart.y + dy
      );

      setTransform(newTransform);
    }

    function handlePointerUp(event) {
      if (!isPanning) return;

      isPanning = false;
      element.releasePointerCapture(event.pointerId);
      element.style.cursor = 'grab';
    }

    // === Gesture Events (trackpad pinch on Safari) ===
    let gestureStartTransform = null;
    let gestureStartCenter = null;

    function handleGestureStart(event) {
      event.preventDefault();
      gestureStartTransform = transform;

      // Get center of element in SVG coordinates
      const rect = element.getBoundingClientRect();
      const screenCenterX = rect.left + rect.width / 2;
      const screenCenterY = rect.top + rect.height / 2;
      gestureStartCenter = toSVGCoords(screenCenterX, screenCenterY);
    }

    function handleGestureChange(event) {
      event.preventDefault();
      if (!gestureStartTransform) return;

      const newK = gestureStartTransform.k * event.scale;
      const newTransform = zoomAround(gestureStartTransform, gestureStartCenter, newK);

      setTransform(newTransform);
    }

    function handleGestureEnd(event) {
      event.preventDefault();
      gestureStartTransform = null;
    }

    // === Attach Event Listeners ===
    element.addEventListener('wheel', handleWheel, { passive: false });
    element.addEventListener('pointerdown', handlePointerDown);
    element.addEventListener('pointermove', handlePointerMove);
    element.addEventListener('pointerup', handlePointerUp);
    element.addEventListener('pointercancel', handlePointerUp);

    // Safari gesture events for trackpad pinch
    element.addEventListener('gesturestart', handleGestureStart);
    element.addEventListener('gesturechange', handleGestureChange);
    element.addEventListener('gestureend', handleGestureEnd);

    // Set initial styles
    element.style.cursor = 'grab';
    element.style.touchAction = 'none';

    // Apply initial transform
    if (config.initialTransform) {
      applyTransform();
    }

    // === Return Handle ===
    const handle = {
      // Get current transform
      getTransform: () => ({ k: transform.k, x: transform.x, y: transform.y }),

      // Set transform directly
      setTransform: (t) => () => {
        setTransform(new ZoomTransform(t.k, t.x, t.y));
      },

      // Reset to identity
      resetZoom: () => {
        setTransform(identity);
      },

      // Zoom to specific scale at point
      zoomTo: (k) => (point) => () => {
        const newTransform = zoomAround(transform, [point.x, point.y], k);
        setTransform(newTransform);
      },

      // Zoom in/out by factor at center
      zoomBy: (factor) => () => {
        // Get center in SVG coordinates
        const rect = element.getBoundingClientRect();
        const screenCenterX = rect.left + rect.width / 2;
        const screenCenterY = rect.top + rect.height / 2;
        const center = toSVGCoords(screenCenterX, screenCenterY);
        const newK = transform.k * factor;
        const newTransform = zoomAround(transform, center, newK);
        setTransform(newTransform);
      },

      // Cleanup
      destroy: () => {
        element.removeEventListener('wheel', handleWheel);
        element.removeEventListener('pointerdown', handlePointerDown);
        element.removeEventListener('pointermove', handlePointerMove);
        element.removeEventListener('pointerup', handlePointerUp);
        element.removeEventListener('pointercancel', handlePointerUp);
        element.removeEventListener('gesturestart', handleGestureStart);
        element.removeEventListener('gesturechange', handleGestureChange);
        element.removeEventListener('gestureend', handleGestureEnd);
        element.style.cursor = '';
        element.style.touchAction = '';
      }
    };

    return handle;
  };
}

// =============================================================================
// Simple Zoom API (compatible with existing attachZoom_)
// =============================================================================

/**
 * Attach zoom behavior (simplified API matching existing attachZoom_)
 */
export function attachZoomNative_(element) {
  return scaleMin => scaleMax => targetSelector => () => {
    return attachNativeZoom_(element)({
      scaleMin,
      scaleMax,
      targetSelector,
      initialTransform: null,
      translateExtent: null,
      onZoom: null
    })();
  };
}

/**
 * Attach zoom with initial transform (matching attachZoomWithTransform_)
 */
export function attachZoomWithTransformNative_(element) {
  return scaleMin => scaleMax => targetSelector => initialTransform => () => {
    return attachNativeZoom_(element)({
      scaleMin,
      scaleMax,
      targetSelector,
      initialTransform,
      translateExtent: null,
      onZoom: null
    })();
  };
}

/**
 * Attach zoom with callback (matching attachZoomWithCallback_)
 */
export function attachZoomWithCallbackNative_(element) {
  return scaleMin => scaleMax => targetSelector => initialTransform => onZoom => () => {
    return attachNativeZoom_(element)({
      scaleMin,
      scaleMax,
      targetSelector,
      initialTransform,
      translateExtent: null,
      onZoom
    })();
  };
}
