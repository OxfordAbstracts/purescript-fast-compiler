// Native Pointer Events implementation - no D3 dependency
// Uses modern browser APIs: pointerdown, pointermove, pointerup, setPointerCapture

/**
 * Attach drag behavior using native Pointer Events
 *
 * @param {Element} element - DOM element to make draggable
 * @param {Object} config - { onStart, onDrag, onEnd }
 *   - onStart: (datum, x, y) -> Effect Unit
 *   - onDrag: (datum, x, y, dx, dy) -> Effect Unit
 *   - onEnd: (datum, x, y) -> Effect Unit
 * @returns {Effect (Effect Unit)} - Returns cleanup function
 */
export function attachPointerDrag_(element) {
  return config => () => {
    let isDragging = false;
    let startX = 0;
    let startY = 0;
    let lastX = 0;
    let lastY = 0;

    function handlePointerDown(event) {
      // Only handle primary button (left click / single touch)
      if (event.button !== 0) return;

      isDragging = true;
      startX = event.clientX;
      startY = event.clientY;
      lastX = startX;
      lastY = startY;

      // Capture pointer - this is the key! Events continue even outside element
      element.setPointerCapture(event.pointerId);

      // Prevent text selection during drag
      event.preventDefault();

      // Get datum from element (D3 convention we're keeping)
      const datum = element.__data__;

      // Call PureScript onStart handler
      config.onStart(datum)(event.clientX)(event.clientY)();
    }

    function handlePointerMove(event) {
      if (!isDragging) return;

      const x = event.clientX;
      const y = event.clientY;
      const dx = x - lastX;
      const dy = y - lastY;
      lastX = x;
      lastY = y;

      const datum = element.__data__;

      // Call PureScript onDrag handler
      config.onDrag(datum)(x)(y)(dx)(dy)();
    }

    function handlePointerUp(event) {
      if (!isDragging) return;

      isDragging = false;

      // Release capture
      element.releasePointerCapture(event.pointerId);

      const datum = element.__data__;

      // Call PureScript onEnd handler
      config.onEnd(datum)(event.clientX)(event.clientY)();
    }

    // Prevent browser's native drag (for images, etc)
    function handleDragStart(event) {
      event.preventDefault();
    }

    // Add event listeners
    element.addEventListener('pointerdown', handlePointerDown);
    element.addEventListener('pointermove', handlePointerMove);
    element.addEventListener('pointerup', handlePointerUp);
    element.addEventListener('pointercancel', handlePointerUp);
    element.addEventListener('dragstart', handleDragStart);

    // Set cursor and touch-action for better UX
    element.style.cursor = 'grab';
    element.style.touchAction = 'none'; // Prevent browser touch gestures

    // Return cleanup function
    return () => {
      element.removeEventListener('pointerdown', handlePointerDown);
      element.removeEventListener('pointermove', handlePointerMove);
      element.removeEventListener('pointerup', handlePointerUp);
      element.removeEventListener('pointercancel', handlePointerUp);
      element.removeEventListener('dragstart', handleDragStart);
      element.style.cursor = '';
      element.style.touchAction = '';
    };
  };
}

/**
 * Attach simulation-aware drag using Pointer Events
 *
 * When drag starts, reheats the simulation.
 * During drag, updates node's fx/fy to follow pointer.
 * On end, releases fx/fy.
 *
 * @param {Element} element - DOM element (must have __data__ with simulation node)
 * @param {Function} reheatFn - Effect Unit function to reheat simulation
 * @returns {Effect (Effect Unit)} - Returns cleanup function
 */
export function attachSimulationPointerDrag_(element) {
  return reheatFn => () => {
    let isDragging = false;

    function handlePointerDown(event) {
      if (event.button !== 0) return;

      isDragging = true;
      element.setPointerCapture(event.pointerId);
      event.preventDefault();

      const node = element.__data__;
      if (!node) {
        console.warn('[PointerDrag] No datum on element');
        return;
      }

      // Reheat simulation
      reheatFn();

      // Pin node at current position
      node.fx = node.x;
      node.fy = node.y;

      element.style.cursor = 'grabbing';
    }

    function handlePointerMove(event) {
      if (!isDragging) return;

      const node = element.__data__;
      if (!node) return;

      // Update fixed position to follow pointer
      // We need to convert client coords to simulation space
      // Using the element's parent group CTM includes any zoom transform
      const svg = element.ownerSVGElement;
      if (svg) {
        const pt = svg.createSVGPoint();
        pt.x = event.clientX;
        pt.y = event.clientY;

        // Get CTM from the element's parent (the group inside zoom transform)
        // This accounts for both SVG viewBox AND any zoom/pan transform
        const parentGroup = element.parentElement;
        const ctm = parentGroup?.getScreenCTM?.() || svg.getScreenCTM();
        if (ctm) {
          const svgPt = pt.matrixTransform(ctm.inverse());
          node.fx = svgPt.x;
          node.fy = svgPt.y;
        }
      } else {
        // Fallback for non-SVG contexts
        node.fx = event.clientX;
        node.fy = event.clientY;
      }
    }

    function handlePointerUp(event) {
      if (!isDragging) return;

      isDragging = false;
      element.releasePointerCapture(event.pointerId);

      const node = element.__data__;
      if (node) {
        // Release pin
        node.fx = null;
        node.fy = null;
      }

      element.style.cursor = 'grab';
    }

    function handleDragStart(event) {
      event.preventDefault();
    }

    element.addEventListener('pointerdown', handlePointerDown);
    element.addEventListener('pointermove', handlePointerMove);
    element.addEventListener('pointerup', handlePointerUp);
    element.addEventListener('pointercancel', handlePointerUp);
    element.addEventListener('dragstart', handleDragStart);

    element.style.cursor = 'grab';
    element.style.touchAction = 'none';

    return () => {
      element.removeEventListener('pointerdown', handlePointerDown);
      element.removeEventListener('pointermove', handlePointerMove);
      element.removeEventListener('pointerup', handlePointerUp);
      element.removeEventListener('pointercancel', handlePointerUp);
      element.removeEventListener('dragstart', handleDragStart);
      element.style.cursor = '';
      element.style.touchAction = '';
    };
  };
}

/**
 * Attach simulation-aware drag for nested datum structure
 * Like attachSimulationPointerDrag_ but accesses datum.node for fx/fy
 */
export function attachSimulationPointerDragNested_(element) {
  return reheatFn => () => {
    let isDragging = false;

    function handlePointerDown(event) {
      if (event.button !== 0) return;

      isDragging = true;
      element.setPointerCapture(event.pointerId);
      event.preventDefault();

      const datum = element.__data__;
      const node = datum?.node;
      if (!node) {
        console.warn('[PointerDragNested] No datum.node on element');
        return;
      }

      reheatFn();
      node.fx = node.x;
      node.fy = node.y;
      element.style.cursor = 'grabbing';
    }

    function handlePointerMove(event) {
      if (!isDragging) return;

      const datum = element.__data__;
      const node = datum?.node;
      if (!node) return;

      const svg = element.ownerSVGElement;
      if (svg) {
        const pt = svg.createSVGPoint();
        pt.x = event.clientX;
        pt.y = event.clientY;
        // Get CTM from parent group to account for zoom transform
        const parentGroup = element.parentElement;
        const ctm = parentGroup?.getScreenCTM?.() || svg.getScreenCTM();
        if (ctm) {
          const svgPt = pt.matrixTransform(ctm.inverse());
          node.fx = svgPt.x;
          node.fy = svgPt.y;
        }
      } else {
        node.fx = event.clientX;
        node.fy = event.clientY;
      }
    }

    function handlePointerUp(event) {
      if (!isDragging) return;

      isDragging = false;
      element.releasePointerCapture(event.pointerId);

      const datum = element.__data__;
      const node = datum?.node;
      if (node) {
        node.fx = null;
        node.fy = null;
      }
      element.style.cursor = 'grab';
    }

    function handleDragStart(event) {
      event.preventDefault();
    }

    element.addEventListener('pointerdown', handlePointerDown);
    element.addEventListener('pointermove', handlePointerMove);
    element.addEventListener('pointerup', handlePointerUp);
    element.addEventListener('pointercancel', handlePointerUp);
    element.addEventListener('dragstart', handleDragStart);

    element.style.cursor = 'grab';
    element.style.touchAction = 'none';

    return () => {
      element.removeEventListener('pointerdown', handlePointerDown);
      element.removeEventListener('pointermove', handlePointerMove);
      element.removeEventListener('pointerup', handlePointerUp);
      element.removeEventListener('pointercancel', handlePointerUp);
      element.removeEventListener('dragstart', handleDragStart);
      element.style.cursor = '';
      element.style.touchAction = '';
    };
  };
}

/**
 * Get pointer position relative to an SVG element
 * Replacement for d3-selection's pointer() function
 */
export function pointerPosition_(event) {
  return container => () => {
    if (container.createSVGPoint) {
      // SVG element - transform through CTM
      const pt = container.createSVGPoint();
      pt.x = event.clientX;
      pt.y = event.clientY;
      const ctm = container.getScreenCTM();
      if (ctm) {
        const svgPt = pt.matrixTransform(ctm.inverse());
        return { x: svgPt.x, y: svgPt.y };
      }
    }
    // HTML element - use offset
    const rect = container.getBoundingClientRect();
    return {
      x: event.clientX - rect.left,
      y: event.clientY - rect.top
    };
  };
}

// =============================================================================
// Simple Drag (no simulation)
// =============================================================================

/**
 * Attach simple drag behavior using Pointer Events
 * Moves element via transform attribute
 *
 * @param {Element} element - DOM element to make draggable
 * @returns {Effect Unit}
 */
export function attachSimpleDrag_(element) {
  return () => () => {
    let isDragging = false;
    let transform = { x: 0, y: 0 };

    function handlePointerDown(event) {
      if (event.button !== 0) return;

      isDragging = true;
      element.setPointerCapture(event.pointerId);
      event.preventDefault();
      event.stopPropagation();  // Prevent bubbling to parent handlers

      // Raise element to front (SVG-specific)
      if (element.parentNode) {
        element.parentNode.appendChild(element);
      }

      element.style.cursor = 'grabbing';
    }

    function handlePointerMove(event) {
      if (!isDragging) return;

      // Get movement delta
      const svg = element.ownerSVGElement;
      if (svg) {
        // Convert movement to SVG coordinates
        const pt = svg.createSVGPoint();
        const ctm = svg.getScreenCTM();
        if (ctm) {
          // Get delta in screen coords
          pt.x = event.movementX;
          pt.y = event.movementY;
          // Transform to SVG scale (ignoring translation)
          const scale = ctm.a; // Assumes uniform scaling
          transform.x += event.movementX / scale;
          transform.y += event.movementY / scale;
        } else {
          transform.x += event.movementX;
          transform.y += event.movementY;
        }
      } else {
        transform.x += event.movementX;
        transform.y += event.movementY;
      }

      element.setAttribute('transform', `translate(${transform.x},${transform.y})`);
    }

    function handlePointerUp(event) {
      if (!isDragging) return;

      isDragging = false;
      element.releasePointerCapture(event.pointerId);
      element.style.cursor = 'grab';
    }

    function handlePointerCancel(event) {
      if (!isDragging) return;
      isDragging = false;
      element.releasePointerCapture(event.pointerId);
      element.style.cursor = 'grab';
    }

    function handleDragStart(event) {
      event.preventDefault();
    }

    element.addEventListener('pointerdown', handlePointerDown);
    element.addEventListener('pointermove', handlePointerMove);
    element.addEventListener('pointerup', handlePointerUp);
    element.addEventListener('pointercancel', handlePointerCancel);
    element.addEventListener('dragstart', handleDragStart);

    element.style.cursor = 'grab';
    element.style.touchAction = 'none';

    return element;
  };
}

// =============================================================================
// Simulation Registry (shared with Behavior/FFI.js during transition)
// =============================================================================
// Global registry for named simulations, enabling declarative SimulationDrag
// Each entry maps simulationId -> { reheat: Effect Unit }

const simulationRegistry = new Map();

/**
 * Register a simulation by ID (called from PureScript)
 */
export function registerSimulationForPointer_(simId) {
  return reheatFn => () => {
    simulationRegistry.set(simId, { reheat: reheatFn });
  };
}

/**
 * Unregister a simulation by ID
 */
export function unregisterSimulationForPointer_(simId) {
  return () => {
    simulationRegistry.delete(simId);
  };
}

// Internal helper
function getSimulationReheat(simId) {
  const sim = simulationRegistry.get(simId);
  return sim ? sim.reheat : null;
}

/**
 * Attach simulation-aware drag by simulation ID using Pointer Events
 * Looks up reheat function from registry
 *
 * @param {Element} element - DOM element (must have __data__ with simulation node)
 * @param {string} simId - Registered simulation ID
 * @returns {Element}
 */
export function attachSimulationDragById_(element) {
  return simId => () => {
    let isDragging = false;

    function handlePointerDown(event) {
      if (event.button !== 0) return;

      isDragging = true;
      element.setPointerCapture(event.pointerId);
      event.preventDefault();

      const node = element.__data__;
      if (!node) {
        console.warn('[PointerDrag] No datum on element');
        return;
      }

      // Lookup and call reheat
      const reheat = getSimulationReheat(simId);
      if (reheat) {
        reheat();
      } else {
        console.warn(`[PointerDrag] No simulation registered with ID: ${simId}`);
      }

      // Pin node at current position
      node.fx = node.x;
      node.fy = node.y;

      element.style.cursor = 'grabbing';
    }

    function handlePointerMove(event) {
      if (!isDragging) return;

      const node = element.__data__;
      if (!node) return;

      // Update fixed position to follow pointer
      // Use parent group CTM to account for zoom transform
      const svg = element.ownerSVGElement;
      if (svg) {
        const pt = svg.createSVGPoint();
        pt.x = event.clientX;
        pt.y = event.clientY;

        const parentGroup = element.parentElement;
        const ctm = parentGroup?.getScreenCTM?.() || svg.getScreenCTM();
        if (ctm) {
          const svgPt = pt.matrixTransform(ctm.inverse());
          node.fx = svgPt.x;
          node.fy = svgPt.y;
        }
      } else {
        node.fx = event.clientX;
        node.fy = event.clientY;
      }
    }

    function handlePointerUp(event) {
      if (!isDragging) return;

      isDragging = false;
      element.releasePointerCapture(event.pointerId);

      const node = element.__data__;
      if (node) {
        node.fx = null;
        node.fy = null;
      }

      element.style.cursor = 'grab';
    }

    function handleDragStart(event) {
      event.preventDefault();
    }

    element.addEventListener('pointerdown', handlePointerDown);
    element.addEventListener('pointermove', handlePointerMove);
    element.addEventListener('pointerup', handlePointerUp);
    element.addEventListener('pointercancel', handlePointerUp);
    element.addEventListener('dragstart', handleDragStart);

    element.style.cursor = 'grab';
    element.style.touchAction = 'none';

    return element;
  };
}

/**
 * Attach simulation-aware drag for nested datum structure by ID
 * Like attachSimulationDragById_ but accesses datum.node for fx/fy
 */
export function attachSimulationDragNestedById_(element) {
  return simId => () => {
    let isDragging = false;

    function handlePointerDown(event) {
      if (event.button !== 0) return;

      isDragging = true;
      element.setPointerCapture(event.pointerId);
      event.preventDefault();

      const datum = element.__data__;
      const node = datum?.node;
      if (!node) {
        console.warn('[PointerDragNested] No datum.node on element');
        return;
      }

      const reheat = getSimulationReheat(simId);
      if (reheat) {
        reheat();
      } else {
        console.warn(`[PointerDragNested] No simulation registered with ID: ${simId}`);
      }

      node.fx = node.x;
      node.fy = node.y;
      element.style.cursor = 'grabbing';
    }

    function handlePointerMove(event) {
      if (!isDragging) return;

      const datum = element.__data__;
      const node = datum?.node;
      if (!node) return;

      const svg = element.ownerSVGElement;
      if (svg) {
        const pt = svg.createSVGPoint();
        pt.x = event.clientX;
        pt.y = event.clientY;
        // Get CTM from parent group to account for zoom transform
        const parentGroup = element.parentElement;
        const ctm = parentGroup?.getScreenCTM?.() || svg.getScreenCTM();
        if (ctm) {
          const svgPt = pt.matrixTransform(ctm.inverse());
          node.fx = svgPt.x;
          node.fy = svgPt.y;
        }
      } else {
        node.fx = event.clientX;
        node.fy = event.clientY;
      }
    }

    function handlePointerUp(event) {
      if (!isDragging) return;

      isDragging = false;
      element.releasePointerCapture(event.pointerId);

      const datum = element.__data__;
      const node = datum?.node;
      if (node) {
        node.fx = null;
        node.fy = null;
      }
      element.style.cursor = 'grab';
    }

    function handleDragStart(event) {
      event.preventDefault();
    }

    element.addEventListener('pointerdown', handlePointerDown);
    element.addEventListener('pointermove', handlePointerMove);
    element.addEventListener('pointerup', handlePointerUp);
    element.addEventListener('pointercancel', handlePointerUp);
    element.addEventListener('dragstart', handleDragStart);

    element.style.cursor = 'grab';
    element.style.touchAction = 'none';

    return element;
  };
}
