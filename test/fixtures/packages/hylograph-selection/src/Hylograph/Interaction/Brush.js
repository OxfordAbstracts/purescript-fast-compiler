// Native Brush Implementation using Pointer Events
// No D3 dependency - pure browser APIs
//
// Integrates with PSD3.Interaction.Coordinated for brush-and-link patterns

// =============================================================================
// Core Brush Implementation
// =============================================================================

/**
 * Internal: Create a native brush with configurable axis constraint
 *
 * @param {SVGElement} svg - The SVG element to attach brush to
 * @param {Object} extent - Brush extent { x0, y0, x1, y1 }
 * @param {string} mode - '2d', 'x', or 'y'
 * @param {Function} onStart - Callback when brush starts (box -> Effect Unit)
 * @param {Function} onBrush - Callback during brush (box -> Effect Unit)
 * @param {Function} onEnd - Callback when brush ends (Maybe box -> Effect Unit)
 * @returns {Object} BrushHandle
 */
function createNativeBrush(svg, extent, mode, onStart, onBrush, onEnd) {
  let brushRect = null;
  let startPoint = null;
  let isDragging = false;
  let currentSelection = null;

  // Throttle state for brush callbacks (50ms = 20fps max for expensive operations)
  let lastBrushCallTime = 0;
  let pendingBrushCall = null;
  const BRUSH_THROTTLE_MS = 50;

  // Create brush rectangle (hidden initially)
  brushRect = document.createElementNS('http://www.w3.org/2000/svg', 'rect');
  brushRect.setAttribute('class', 'brush-rect');
  brushRect.setAttribute('fill', 'rgba(74, 158, 255, 0.2)');
  brushRect.setAttribute('stroke', '#4a9eff');
  brushRect.setAttribute('stroke-width', '1');
  brushRect.setAttribute('pointer-events', 'none');
  brushRect.setAttribute('display', 'none');
  svg.appendChild(brushRect);

  // Convert client coords to SVG coords
  function toSvgCoords(event) {
    if (svg.createSVGPoint) {
      const pt = svg.createSVGPoint();
      pt.x = event.clientX;
      pt.y = event.clientY;
      const ctm = svg.getScreenCTM();
      if (ctm) {
        return pt.matrixTransform(ctm.inverse());
      }
    }
    // Fallback
    const rect = svg.getBoundingClientRect();
    return { x: event.clientX - rect.left, y: event.clientY - rect.top };
  }

  // Clamp to extent
  function clamp(val, min, max) {
    return Math.max(min, Math.min(max, val));
  }

  // Update visual rect from selection
  function updateRect(sel) {
    if (!sel) {
      brushRect.setAttribute('display', 'none');
      return;
    }
    brushRect.setAttribute('display', 'block');

    if (mode === 'x') {
      // X-only: full height
      brushRect.setAttribute('x', sel.x0);
      brushRect.setAttribute('y', extent.y0);
      brushRect.setAttribute('width', sel.x1 - sel.x0);
      brushRect.setAttribute('height', extent.y1 - extent.y0);
    } else if (mode === 'y') {
      // Y-only: full width
      brushRect.setAttribute('x', extent.x0);
      brushRect.setAttribute('y', sel.y0);
      brushRect.setAttribute('width', extent.x1 - extent.x0);
      brushRect.setAttribute('height', sel.y1 - sel.y0);
    } else {
      // 2D
      brushRect.setAttribute('x', sel.x0);
      brushRect.setAttribute('y', sel.y0);
      brushRect.setAttribute('width', sel.x1 - sel.x0);
      brushRect.setAttribute('height', sel.y1 - sel.y0);
    }
  }

  function handlePointerDown(event) {
    // Only respond to primary button on background
    if (event.button !== 0) return;

    // Only start brush on SVG background, not on data elements
    const target = event.target;
    const isBrushTarget = target === svg ||
                          target.tagName === 'svg' ||
                          target.classList.contains('brush-background');

    if (!isBrushTarget) return;

    isDragging = true;
    svg.setPointerCapture(event.pointerId);
    event.preventDefault();

    startPoint = toSvgCoords(event);
    startPoint.x = clamp(startPoint.x, extent.x0, extent.x1);
    startPoint.y = clamp(startPoint.y, extent.y0, extent.y1);

    // Initialize selection at start point
    if (mode === 'x') {
      currentSelection = { x0: startPoint.x, x1: startPoint.x };
    } else if (mode === 'y') {
      currentSelection = { y0: startPoint.y, y1: startPoint.y };
    } else {
      currentSelection = { x0: startPoint.x, y0: startPoint.y, x1: startPoint.x, y1: startPoint.y };
    }

    updateRect(currentSelection);
    if (onStart) onStart(currentSelection)();
  }

  function handlePointerMove(event) {
    if (!isDragging) return;

    const currentPoint = toSvgCoords(event);
    currentPoint.x = clamp(currentPoint.x, extent.x0, extent.x1);
    currentPoint.y = clamp(currentPoint.y, extent.y0, extent.y1);

    if (mode === 'x') {
      const x0 = Math.min(startPoint.x, currentPoint.x);
      const x1 = Math.max(startPoint.x, currentPoint.x);
      currentSelection = { x0, x1 };
    } else if (mode === 'y') {
      const y0 = Math.min(startPoint.y, currentPoint.y);
      const y1 = Math.max(startPoint.y, currentPoint.y);
      currentSelection = { y0, y1 };
    } else {
      const x0 = Math.min(startPoint.x, currentPoint.x);
      const y0 = Math.min(startPoint.y, currentPoint.y);
      const x1 = Math.max(startPoint.x, currentPoint.x);
      const y1 = Math.max(startPoint.y, currentPoint.y);
      currentSelection = { x0, y0, x1, y1 };
    }

    // Always update visual rect immediately for smooth feedback
    updateRect(currentSelection);

    // Throttle the expensive callback
    if (onBrush) {
      const now = performance.now();
      if (now - lastBrushCallTime >= BRUSH_THROTTLE_MS) {
        lastBrushCallTime = now;
        if (pendingBrushCall) {
          cancelAnimationFrame(pendingBrushCall);
          pendingBrushCall = null;
        }
        onBrush(currentSelection)();
      } else if (!pendingBrushCall) {
        // Schedule a trailing call to ensure final position is processed
        pendingBrushCall = requestAnimationFrame(() => {
          pendingBrushCall = null;
          lastBrushCallTime = performance.now();
          onBrush(currentSelection)();
        });
      }
    }
  }

  function handlePointerUp(event) {
    if (!isDragging) return;

    isDragging = false;
    svg.releasePointerCapture(event.pointerId);

    // Cancel any pending throttled brush call
    if (pendingBrushCall) {
      cancelAnimationFrame(pendingBrushCall);
      pendingBrushCall = null;
    }

    // If brush is too small, treat as click to clear
    const width = parseFloat(brushRect.getAttribute('width')) || 0;
    const height = parseFloat(brushRect.getAttribute('height')) || 0;
    const minSize = mode === 'x' ? width : mode === 'y' ? height : Math.max(width, height);

    if (minSize < 5) {
      brushRect.setAttribute('display', 'none');
      currentSelection = null;
      if (onEnd) onEnd(null)();
    } else {
      if (onEnd) onEnd(currentSelection)();
    }
  }

  // Attach event listeners
  svg.addEventListener('pointerdown', handlePointerDown);
  svg.addEventListener('pointermove', handlePointerMove);
  svg.addEventListener('pointerup', handlePointerUp);
  svg.addEventListener('pointercancel', handlePointerUp);

  // Return handle for programmatic control
  const handle = {
    clear: () => {
      brushRect.setAttribute('display', 'none');
      currentSelection = null;
    },
    move: (newSelection) => {
      currentSelection = newSelection;
      updateRect(newSelection);
    },
    getSelection: () => currentSelection,
    destroy: () => {
      if (pendingBrushCall) {
        cancelAnimationFrame(pendingBrushCall);
        pendingBrushCall = null;
      }
      svg.removeEventListener('pointerdown', handlePointerDown);
      svg.removeEventListener('pointermove', handlePointerMove);
      svg.removeEventListener('pointerup', handlePointerUp);
      svg.removeEventListener('pointercancel', handlePointerUp);
      if (brushRect.parentNode) {
        brushRect.parentNode.removeChild(brushRect);
      }
    }
  };

  return handle;
}

// =============================================================================
// Public API - Basic Brush
// =============================================================================

/**
 * Attach native 2D brush behavior to an SVG element
 */
export function attachNativeBrush_(svg) {
  return extent => onBrush => onEnd => () => {
    return createNativeBrush(svg, extent, '2d', null, onBrush, onEnd);
  };
}

/**
 * Attach native 2D brush with all callbacks (onStart, onBrush, onEnd)
 * Compatible with old d3-brush API
 */
export function attachNativeBrushFull_(svg) {
  return extent => onStart => onBrush => onEnd => () => {
    return createNativeBrush(svg, extent, '2d', onStart, onBrush, onEnd);
  };
}

/**
 * Attach native horizontal (X-only) brush
 */
export function attachNativeBrushX_(svg) {
  return extent => onStart => onBrush => onEnd => () => {
    return createNativeBrush(svg, extent, 'x', onStart, onBrush, onEnd);
  };
}

/**
 * Attach native vertical (Y-only) brush
 */
export function attachNativeBrushY_(svg) {
  return extent => onStart => onBrush => onEnd => () => {
    return createNativeBrush(svg, extent, 'y', onStart, onBrush, onEnd);
  };
}

// =============================================================================
// Public API - Coordinated Brush
// =============================================================================

/**
 * Attach brush that integrates with Coordinated framework
 * Automatically emits BrushTrigger to the specified group
 */
export function attachCoordinatedBrush_(svg) {
  return extent => groupName => emitTriggerFn => mkBrushTriggerFn => mkClearTriggerFn => () => {
    const handle = createNativeBrush(
      svg, extent, '2d',
      // onStart - also emit brush trigger
      (box) => () => {
        const trigger = mkBrushTriggerFn(box);
        emitTriggerFn(groupName)(trigger)();
      },
      // onBrush
      (box) => () => {
        const trigger = mkBrushTriggerFn(box);
        emitTriggerFn(groupName)(trigger)();
      },
      // onEnd
      (maybeBox) => () => {
        if (maybeBox) {
          const trigger = mkBrushTriggerFn(maybeBox);
          emitTriggerFn(groupName)(trigger)();
        } else {
          const trigger = mkClearTriggerFn();
          emitTriggerFn(groupName)(trigger)();
        }
      }
    );

    return handle;
  };
}

// =============================================================================
// Public API - Handle Operations
// =============================================================================

/**
 * Clear brush programmatically
 */
export function clearBrush_(handle) {
  return () => {
    handle.clear();
  };
}

/**
 * Move brush selection programmatically
 */
export function moveBrush_(handle) {
  return selection => () => {
    handle.move(selection);
  };
}

/**
 * Get current brush selection
 */
export function getBrushSelection_(handle) {
  return () => {
    return handle.getSelection();
  };
}

/**
 * Destroy brush (remove event listeners and DOM element)
 */
export function destroyBrush_(handle) {
  return () => {
    handle.destroy();
  };
}
