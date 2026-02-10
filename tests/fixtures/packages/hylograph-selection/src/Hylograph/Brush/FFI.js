// FFI for D3 brush behavior
// NOTE: Native Pointer Events implementation - d3-brush REMOVED
// D3 dependencies: NONE

// =============================================================================
// Core Brush Implementation (inlined from PSD3.Interaction.Brush)
// =============================================================================

/**
 * Internal: Create a native brush with configurable axis constraint
 */
function createNativeBrush(svg, extent, mode, onStart, onBrush, onEnd) {
  let brushRect = null;
  let startPoint = null;
  let isDragging = false;
  let currentSelection = null;

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

    updateRect(currentSelection);
    if (onBrush) onBrush(currentSelection)();
  }

  function handlePointerUp(event) {
    if (!isDragging) return;

    isDragging = false;
    svg.releasePointerCapture(event.pointerId);

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
// Public API (matches original d3-brush API)
// =============================================================================

/**
 * Create and attach a 2D brush to an element
 */
export function attachBrush_(element) {
  return extent => onStart => onBrush => onEnd => () => {
    return createNativeBrush(element, extent, '2d', onStart, onBrush, onEnd);
  };
}

/**
 * Create and attach a 1D horizontal brush (brushX)
 */
export function attachBrushX_(element) {
  return extent => onStart => onBrush => onEnd => () => {
    return createNativeBrush(element, extent, 'x', onStart, onBrush, onEnd);
  };
}

/**
 * Create and attach a 1D vertical brush (brushY)
 */
export function attachBrushY_(element) {
  return extent => onStart => onBrush => onEnd => () => {
    return createNativeBrush(element, extent, 'y', onStart, onBrush, onEnd);
  };
}

/**
 * Clear brush selection programmatically
 */
export function clearBrush_(brushHandle) {
  return () => {
    brushHandle.clear();
  };
}

/**
 * Move brush selection programmatically
 */
export function moveBrush_(brushHandle) {
  return selection => () => {
    brushHandle.move(selection);
  };
}

/**
 * Get current brush selection
 */
export function getBrushSelection_(brushHandle) {
  return () => {
    return brushHandle.getSelection();
  };
}
