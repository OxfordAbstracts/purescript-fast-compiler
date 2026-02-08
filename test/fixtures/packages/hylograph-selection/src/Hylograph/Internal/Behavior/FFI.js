// FFI for behaviors (zoom, drag, mouse events)
// NO D3 DEPENDENCIES - using native DOM and Pointer Events
import {
  registerSimulationForPointer_,
  unregisterSimulationForPointer_,
  attachSimpleDrag_ as nativeSimpleDrag,
  attachSimulationDragById_ as nativeSimulationDragById,
  attachSimulationDragNestedById_ as nativeSimulationDragNestedById
} from "../Hylograph.Interaction.Pointer/foreign.js";
import {
  attachZoomNative_,
  attachZoomWithTransformNative_,
  attachZoomWithCallbackNative_
} from "../Hylograph.Interaction.Zoom/foreign.js";

/**
 * Update an element's attribute by selector
 * @param {string} selector - CSS selector
 * @param {string} attr - Attribute name
 * @param {string} value - Attribute value
 */
export function updateAttr_(selector) {
  return attr => value => () => {
    const element = document.querySelector(selector);
    if (element) {
      element.setAttribute(attr, value);
    }
  };
}

// =============================================================================
// Simulation Registry
// =============================================================================
// Delegates to Pointer.js for the actual registry - this ensures
// BehaviorFFI.registerSimulation_ and Pointer.attachSimulationDragById
// share the same registry.

/**
 * Register a simulation by ID
 * @param {string} simId - Unique identifier for the simulation
 * @param {Function} reheatFn - PureScript Effect Unit function to reheat the simulation
 */
export function registerSimulation_(simId) {
  return reheatFn => () => {
    // Delegate to Pointer module's registry
    registerSimulationForPointer_(simId)(reheatFn)();
  };
}

/**
 * Unregister a simulation by ID
 * @param {string} simId - The simulation ID to remove
 */
export function unregisterSimulation_(simId) {
  return () => {
    // Delegate to Pointer module's registry
    unregisterSimulationForPointer_(simId)();
  };
}

/**
 * Attach simulation-aware drag behavior using the registry
 * DELEGATES to native Pointer Events implementation
 * @param {Element} element - The DOM element to attach drag to
 * @param {string} simId - The registered simulation ID
 * @returns {Element} The element (for chaining)
 */
export function attachSimulationDragById_(element) {
  return simId => () => {
    return nativeSimulationDragById(element)(simId)();
  };
}

/**
 * Attach simulation-aware drag for nested datum structure
 * DELEGATES to native Pointer Events implementation
 * @param {Element} element - The DOM element to attach drag to
 * @param {string} simId - The registered simulation ID
 * @returns {Element} The element (for chaining)
 */
export function attachSimulationDragNestedById_(element) {
  return simId => () => {
    return nativeSimulationDragNestedById(element)(simId)();
  };
}

/**
 * Attach zoom behavior to an element
 * DELEGATES to native Pointer Events implementation
 * @param {Element} element - The DOM element to attach zoom to (typically SVG)
 * @param {number} scaleMin - Minimum zoom scale
 * @param {number} scaleMax - Maximum zoom scale
 * @param {string} targetSelector - CSS selector for the element to transform
 * @returns {Element} The element (for chaining)
 */
export function attachZoom_(element) {
  return scaleMin => scaleMax => targetSelector => () => {
    // Delegate to native zoom implementation
    attachZoomNative_(element)(scaleMin)(scaleMax)(targetSelector)();
    return element;
  };
}

/**
 * Get the current zoom transform from an element
 * Returns {k, x, y} or identity transform if none set
 * Compatible with both native zoom and D3 zoom (both store __zoom property)
 * @param {Element} element - The DOM element with zoom behavior
 * @returns {{k: number, x: number, y: number}} The zoom transform
 */
export function getZoomTransform_(element) {
  return () => {
    // Native zoom stores transform on element.__zoom (same as D3 convention)
    const t = element.__zoom;
    if (t && typeof t.k === 'number') {
      return { k: t.k, x: t.x, y: t.y };
    }
    // Return identity if no transform exists
    return { k: 1, x: 0, y: 0 };
  };
}

/**
 * Attach zoom behavior and restore a previous transform
 * DELEGATES to native Pointer Events implementation
 * @param {Element} element - The DOM element to attach zoom to
 * @param {number} scaleMin - Minimum zoom scale
 * @param {number} scaleMax - Maximum zoom scale
 * @param {string} targetSelector - CSS selector for the element to transform
 * @param {{k: number, x: number, y: number}} transform - Transform to restore
 * @returns {Element} The element (for chaining)
 */
export function attachZoomWithTransform_(element) {
  return scaleMin => scaleMax => targetSelector => transform => () => {
    // Delegate to native zoom implementation
    attachZoomWithTransformNative_(element)(scaleMin)(scaleMax)(targetSelector)(transform)();
    return element;
  };
}

/**
 * Attach zoom behavior with callback on zoom events
 * DELEGATES to native Pointer Events implementation
 * Like attachZoomWithTransform_ but also calls a callback with the current transform
 * @param {Element} element - The DOM element to attach zoom to
 * @param {number} scaleMin - Minimum zoom scale
 * @param {number} scaleMax - Maximum zoom scale
 * @param {string} targetSelector - CSS selector for the element to transform
 * @param {{k: number, x: number, y: number}} initialTransform - Transform to restore
 * @param {Function} onZoom - PureScript (ZoomTransform -> Effect Unit) callback
 * @returns {Element} The element (for chaining)
 */
export function attachZoomWithCallback_(element) {
  return scaleMin => scaleMax => targetSelector => initialTransform => onZoom => () => {
    // Delegate to native zoom implementation
    attachZoomWithCallbackNative_(element)(scaleMin)(scaleMax)(targetSelector)(initialTransform)(onZoom)();
    return element;
  };
}

/**
 * Attach simple drag behavior to an element
 * DELEGATES to native Pointer Events implementation
 * @param {Element} element - The DOM element to attach drag to
 * @returns {Element} The element (for chaining)
 */
export function attachSimpleDrag_(element) {
  return () => () => {
    return nativeSimpleDrag(element)()();
  };
}

/**
 * DEPRECATED: Attach simulation-aware drag behavior to an element
 *
 * This function is deprecated. Use registerSimulation_ + attachSimulationDragById_ instead,
 * or use PSD3.Interaction.Pointer.attachSimulationDrag with a reheat function.
 *
 * @param {Element} element - The DOM element to attach drag to
 * @param {d3.Simulation|null} simulation - The D3 force simulation (IGNORED)
 * @param {string} label - Event namespace label (IGNORED)
 * @throws {Error} This function is deprecated
 */
export function attachSimulationDrag_(element) {
  return simulation => label => () => {
    console.error(
      '[DEPRECATED] attachSimulationDrag_ is deprecated. ' +
      'Use registerSimulation_ + Drag (SimulationDrag simId), ' +
      'or PSD3.Interaction.Pointer.attachSimulationDrag with a reheat function.'
    );
    throw new Error('attachSimulationDrag_ is deprecated - use registry-based drag instead');
  };
}

/**
 * Attach click handler without datum access
 * @param {Element} element - The DOM element to attach click handler to
 * @param {Function} handler - The PureScript Effect Unit handler
 * @returns {Element} The element (for chaining)
 */
export function attachClick_(element) {
  return handler => () => {
    element.addEventListener('click', function(event) {
      event.stopPropagation();  // Prevent bubbling to parent handlers
      // Call PureScript handler (it's already an Effect, so invoke it)
      handler();
    });

    // Set cursor to pointer for clickable elements
    element.style.cursor = 'pointer';

    return element;
  };
}

/**
 * Attach click handler with datum access
 * @param {Element} element - The DOM element to attach click handler to
 * @param {Function} handler - The PureScript (datum -> Effect Unit) handler
 * @returns {Element} The element (for chaining)
 */
export function attachClickWithDatum_(element) {
  return handler => () => {
    element.addEventListener('click', function(event) {
      event.stopPropagation();  // Prevent bubbling to parent handlers
      // Get datum from element's __data__ property (D3 convention)
      const d = this.__data__;
      // Call PureScript handler with datum (it returns an Effect, so invoke it)
      handler(d)();
    });

    // Set cursor to pointer for clickable elements
    element.style.cursor = 'pointer';

    return element;
  };
}

/**
 * Attach mouseenter handler with datum access
 * @param {Element} element - The DOM element to attach handler to
 * @param {Function} handler - The PureScript (datum -> Effect Unit) handler
 * @returns {Element} The element (for chaining)
 */
export function attachMouseEnter_(element) {
  return handler => () => {
    element.addEventListener('mouseenter', function(event) {
      // Get datum from element's __data__ property (D3 convention)
      const d = this.__data__;
      // Call PureScript handler with datum (it returns an Effect, so invoke it)
      handler(d)();
    });

    return element;
  };
}

/**
 * Attach mouseleave handler with datum access
 * @param {Element} element - The DOM element to attach handler to
 * @param {Function} handler - The PureScript (datum -> Effect Unit) handler
 * @returns {Element} The element (for chaining)
 */
export function attachMouseLeave_(element) {
  return handler => () => {
    element.addEventListener('mouseleave', function(event) {
      // Get datum from element's __data__ property (D3 convention)
      const d = this.__data__;
      // Call PureScript handler with datum (it returns an Effect, so invoke it)
      handler(d)();
    });

    return element;
  };
}

/**
 * Attach hover highlight behavior
 * @param {Element} element - The DOM element to attach to
 * @param {Array} enterStyles - Array of {attr, value} to apply on enter
 * @param {Array} leaveStyles - Array of {attr, value} to apply on leave
 * @returns {Element} The element (for chaining)
 */
export function attachHighlight_(element) {
  return enterStyles => leaveStyles => () => {
    element.addEventListener('mouseenter', function(event) {
      // Raise element to front
      if (this.parentNode) {
        this.parentNode.appendChild(this);
      }
      // Apply enter styles
      enterStyles.forEach(style => {
        this.setAttribute(style.attr, style.value);
      });
    });

    element.addEventListener('mouseleave', function(event) {
      // Apply leave styles
      leaveStyles.forEach(style => {
        this.setAttribute(style.attr, style.value);
      });
    });

    return element;
  };
}

/**
 * Attach mousemove handler using pure web-events (no D3)
 * @param {Element} element - The DOM element to attach handler to
 * @param {Function} handler - The PureScript EffectFn2 datum MouseEvent Unit handler
 * @returns {Element} The element (for chaining)
 */
export function attachMouseMoveWithEvent_(element) {
  return handler => () => {
    element.addEventListener('mousemove', function(event) {
      // Get datum from element's __data__ property (D3 convention)
      const datum = this.__data__;
      handler(datum, event);
    });
    return element;
  };
}

/**
 * DEPRECATED: D3-based version - use attachMouseMoveWithEvent_ instead
 */
export function attachMouseMoveWithInfo_(element) {
  return handler => () => {
    element.addEventListener('mousemove', function(event) {
      const d = this.__data__;
      const info = {
        clientX: event.clientX,
        clientY: event.clientY,
        pageX: event.pageX,
        pageY: event.pageY,
        offsetX: event.offsetX,
        offsetY: event.offsetY
      };
      handler(d)(info)();
    });

    return element;
  };
}

/**
 * Attach mouseenter handler using pure web-events (no D3)
 */
export function attachMouseEnterWithEvent_(element) {
  return handler => () => {
    element.addEventListener('mouseenter', function(event) {
      const datum = this.__data__;
      handler(datum, event);
    });
    return element;
  };
}

/**
 * DEPRECATED: D3-based version
 */
export function attachMouseEnterWithInfo_(element) {
  return handler => () => {
    element.addEventListener('mouseenter', function(event) {
      const d = this.__data__;
      const info = {
        clientX: event.clientX,
        clientY: event.clientY,
        pageX: event.pageX,
        pageY: event.pageY,
        offsetX: event.offsetX,
        offsetY: event.offsetY
      };
      handler(d)(info)();
    });

    return element;
  };
}

/**
 * Attach mouseleave handler using pure web-events (no D3)
 */
export function attachMouseLeaveWithEvent_(element) {
  return handler => () => {
    element.addEventListener('mouseleave', function(event) {
      const datum = this.__data__;
      handler(datum, event);
    });
    return element;
  };
}

/**
 * DEPRECATED: D3-based version
 */
export function attachMouseLeaveWithInfo_(element) {
  return handler => () => {
    element.addEventListener('mouseleave', function(event) {
      const d = this.__data__;
      const info = {
        clientX: event.clientX,
        clientY: event.clientY,
        pageX: event.pageX,
        pageY: event.pageY,
        offsetX: event.offsetX,
        offsetY: event.offsetY
      };
      handler(d)(info)();
    });

    return element;
  };
}

/**
 * Attach mousedown handler without datum access
 * @param {Element} element - The DOM element to attach handler to
 * @param {Function} handler - The PureScript Effect Unit handler
 * @returns {Element} The element (for chaining)
 */
export function attachMouseDown_(element) {
  return handler => () => {
    element.addEventListener('mousedown', function(event) {
      // Call PureScript handler
      handler();
    });

    return element;
  };
}

/**
 * Attach mousedown handler with event info (using web-events)
 * @param {Element} element - The DOM element to attach handler to
 * @param {Function} handler - The PureScript EffectFn2 datum MouseEvent Unit handler
 * @returns {Element} The element (for chaining)
 */
export function attachMouseDownWithEvent_(element) {
  return handler => () => {
    element.addEventListener('mousedown', function(event) {
      const datum = this.__data__;
      handler(datum, event);
    });
    return element;
  };
}

// =============================================================================
// SVG Coordinate Utilities
// =============================================================================

/**
 * Get mouse position relative to an SVG element (replaces d3.pointer)
 * @param {MouseEvent} event - The mouse event
 * @param {SVGElement} svgElement - The SVG element to get coordinates relative to
 * @returns {[number, number]} [x, y] coordinates
 */
function getSvgPointer(event, svgElement) {
  const pt = svgElement.createSVGPoint();
  pt.x = event.clientX;
  pt.y = event.clientY;
  const ctm = svgElement.getScreenCTM();
  if (ctm) {
    const svgP = pt.matrixTransform(ctm.inverse());
    return [svgP.x, svgP.y];
  }
  // Fallback to offset if CTM not available
  return [event.offsetX, event.offsetY];
}

/**
 * Attach line chart tooltip behavior
 * Shows series name and interpolated value at mouse position
 */
export function attachLineTooltip_(svgElement) {
  return pathElement => seriesName => points => margin => () => {
    // Get or create tooltip div
    let tooltip = document.querySelector('.line-tooltip');
    if (!tooltip) {
      tooltip = document.createElement('div');
      tooltip.className = 'line-tooltip';
      tooltip.style.cssText = `
        position: absolute;
        background: rgba(0, 0, 0, 0.8);
        color: white;
        padding: 8px 12px;
        border-radius: 4px;
        font-size: 12px;
        pointer-events: none;
        opacity: 0;
        z-index: 1000;
      `;
      document.body.appendChild(tooltip);
    }

    // Sort points by x for binary search
    const sortedPoints = [...points].sort((a, b) => a.x - b.x);

    // Find nearest point by x coordinate
    function findNearestPoint(mouseX) {
      // Adjust for margin
      const x = mouseX - margin.left;

      // Binary search for nearest point
      let left = 0;
      let right = sortedPoints.length - 1;

      while (right - left > 1) {
        const mid = Math.floor((left + right) / 2);
        if (sortedPoints[mid].x < x) {
          left = mid;
        } else {
          right = mid;
        }
      }

      // Return closer of the two
      if (right >= sortedPoints.length) return sortedPoints[left];
      if (left < 0) return sortedPoints[right];

      const dLeft = Math.abs(sortedPoints[left].x - x);
      const dRight = Math.abs(sortedPoints[right].x - x);
      return dLeft < dRight ? sortedPoints[left] : sortedPoints[right];
    }

    // Attach events
    pathElement.addEventListener('mouseenter', function(event) {
      // Highlight the line - raise it to front
      if (this.parentNode) {
        this.parentNode.appendChild(this);
      }
      this.setAttribute('stroke', '#333');
      this.setAttribute('stroke-width', '2.5');

      tooltip.style.opacity = '1';
    });

    pathElement.addEventListener('mousemove', function(event) {
      // Get mouse position relative to SVG
      const [mouseX, mouseY] = getSvgPointer(event, svgElement);

      // Find nearest data point
      const point = findNearestPoint(mouseX);

      // Update tooltip content
      tooltip.innerHTML = `<strong>${seriesName}</strong><br/>${point.label}: ${point.y.toFixed(1)}%`;
      tooltip.style.left = (event.pageX + 15) + 'px';
      tooltip.style.top = (event.pageY - 10) + 'px';
    });

    pathElement.addEventListener('mouseleave', function(event) {
      // Reset line style
      this.setAttribute('stroke', '#ddd');
      this.setAttribute('stroke-width', '1.5');

      tooltip.style.opacity = '0';
    });

    return pathElement;
  };
}

// =============================================================================
// Tier 2: Coordinated Highlighting
// =============================================================================

// Global registry of elements participating in coordinated highlighting
// Key: group name (or "_global" for ungrouped)
// Value: Array of { element, datum, identifyFn, classifyFn }
const highlightRegistry = new Map();

// CSS class names
const HIGHLIGHT_PRIMARY = 'highlight-primary';
const HIGHLIGHT_RELATED = 'highlight-related';
const HIGHLIGHT_DIMMED = 'highlight-dimmed';
const HIGHLIGHT_UPSTREAM = 'highlight-upstream';
const HIGHLIGHT_DOWNSTREAM = 'highlight-downstream';
const ALL_HIGHLIGHT_CLASSES = [HIGHLIGHT_PRIMARY, HIGHLIGHT_RELATED, HIGHLIGHT_DIMMED, HIGHLIGHT_UPSTREAM, HIGHLIGHT_DOWNSTREAM];

// TODO: TECH DEBT - These enum mappings assume specific Int representation from PureScript
// highlightClassToInt and tooltipTriggerToInt. This is fragile. A safer approach would be
// to pass the class name as a string or use a tagged union that can be introspected.
// For now, the PureScript side explicitly converts via highlightClassToInt/tooltipTriggerToInt
// in Operations.purs to ensure alignment.
const HC_PRIMARY = 0;
const HC_RELATED = 1;
const HC_DIMMED = 2;
const HC_NEUTRAL = 3;
const HC_UPSTREAM = 4;
const HC_DOWNSTREAM = 5;

const TT_ON_HOVER = 0;
const TT_WHEN_PRIMARY = 1;
const TT_WHEN_RELATED = 2;

// =============================================================================
// Tooltip Management
// =============================================================================

// Container for all coordinated tooltips
let tooltipContainer = null;
// Map of element -> tooltip div (for WhenPrimary/WhenRelated tooltips)
const elementTooltips = new Map();
// The currently active hover tooltip (for OnHover)
let hoverTooltip = null;

/**
 * Get or create the tooltip container
 */
function getTooltipContainer() {
  if (!tooltipContainer) {
    tooltipContainer = document.createElement('div');
    tooltipContainer.className = 'coordinated-tooltip-container';
    tooltipContainer.style.cssText = 'position: fixed; top: 0; left: 0; pointer-events: none; z-index: 10000;';
    document.body.appendChild(tooltipContainer);
  }
  return tooltipContainer;
}

/**
 * Create a tooltip element
 * @returns {HTMLDivElement}
 */
function createTooltipElement() {
  const tooltip = document.createElement('div');
  tooltip.className = 'coordinated-tooltip';
  tooltip.style.cssText = `
    position: absolute;
    background: rgba(15, 23, 42, 0.95);
    color: #e2e8f0;
    padding: 6px 10px;
    border-radius: 4px;
    font-size: 12px;
    font-family: system-ui, -apple-system, sans-serif;
    white-space: nowrap;
    pointer-events: none;
    opacity: 0;
    transition: opacity 0.15s ease-in-out;
    box-shadow: 0 4px 6px -1px rgba(0, 0, 0, 0.1), 0 2px 4px -1px rgba(0, 0, 0, 0.06);
    border: 1px solid rgba(148, 163, 184, 0.2);
  `;
  getTooltipContainer().appendChild(tooltip);
  return tooltip;
}

/**
 * Position a tooltip near an element
 * @param {HTMLElement} tooltip - The tooltip element
 * @param {Element} targetElement - The element to position near
 */
function positionTooltipNearElement(tooltip, targetElement) {
  const rect = targetElement.getBoundingClientRect();
  const tooltipRect = tooltip.getBoundingClientRect();

  // Position above the element, centered
  let x = rect.left + rect.width / 2 - tooltipRect.width / 2;
  let y = rect.top - tooltipRect.height - 8;

  // Keep within viewport
  x = Math.max(8, Math.min(x, window.innerWidth - tooltipRect.width - 8));
  if (y < 8) {
    // Position below if not enough space above
    y = rect.bottom + 8;
  }

  tooltip.style.left = `${x}px`;
  tooltip.style.top = `${y}px`;
}

/**
 * Position a tooltip at mouse position
 * @param {HTMLElement} tooltip - The tooltip element
 * @param {MouseEvent} event - The mouse event
 */
function positionTooltipAtMouse(tooltip, event) {
  const x = event.clientX + 12;
  const y = event.clientY - 8;
  tooltip.style.left = `${x}px`;
  tooltip.style.top = `${y}px`;
}

/**
 * Show a tooltip with content
 * @param {HTMLElement} tooltip - The tooltip element
 * @param {string} content - The text content
 */
function showTooltip(tooltip, content) {
  tooltip.textContent = content;
  tooltip.style.opacity = '1';
}

/**
 * Hide a tooltip
 * @param {HTMLElement} tooltip - The tooltip element
 */
function hideTooltip(tooltip) {
  if (tooltip) {
    tooltip.style.opacity = '0';
  }
}

/**
 * Hide all tooltips
 */
function hideAllTooltips() {
  if (hoverTooltip) {
    hideTooltip(hoverTooltip);
  }
  elementTooltips.forEach(tooltip => hideTooltip(tooltip));
}

/**
 * Get or create a highlight group
 * @param {string|null} groupName - Group name or null for global
 * @returns {Array} The group's element array
 */
function getHighlightGroup(groupName) {
  const key = groupName || '_global';
  if (!highlightRegistry.has(key)) {
    highlightRegistry.set(key, []);
  }
  return highlightRegistry.get(key);
}

/**
 * Apply highlight classes and tooltips to all elements in a group based on hovered id
 * @param {string|null} groupName - Group name
 * @param {string} hoveredId - The identity of the hovered element
 * @param {Element} triggerElement - The element that triggered the highlight (for OnHover tooltips)
 * @param {MouseEvent|null} event - The mouse event (for positioning OnHover tooltips)
 */
function applyHighlights(groupName, hoveredId, triggerElement, event) {
  const group = getHighlightGroup(groupName);

  group.forEach(entry => {
    const { element, classifyFn, tooltipContentFn, tooltipTrigger } = entry;
    // IMPORTANT: Read datum fresh from element, not from cached entry
    // because __data__ may not have been set when behavior was attached
    const datum = element.__data__;

    // Remove all highlight classes first
    ALL_HIGHLIGHT_CLASSES.forEach(cls => element.classList.remove(cls));

    // Skip if no datum bound to element
    if (!datum) {
      return;
    }

    // Get classification from PureScript function
    // classifyFn is curried: hoveredId -> datum -> Int
    const classification = classifyFn(hoveredId)(datum);

    // Apply appropriate class
    switch (classification) {
      case HC_PRIMARY:
        element.classList.add(HIGHLIGHT_PRIMARY);
        break;
      case HC_RELATED:
        element.classList.add(HIGHLIGHT_RELATED);
        break;
      case HC_DIMMED:
        element.classList.add(HIGHLIGHT_DIMMED);
        break;
      case HC_UPSTREAM:
        element.classList.add(HIGHLIGHT_UPSTREAM);
        break;
      case HC_DOWNSTREAM:
        element.classList.add(HIGHLIGHT_DOWNSTREAM);
        break;
      case HC_NEUTRAL:
      default:
        // No class applied
        break;
    }

    // Handle tooltips if configured
    if (tooltipContentFn) {
      const content = tooltipContentFn(datum);
      const shouldShow =
        (tooltipTrigger === TT_ON_HOVER && element === triggerElement) ||
        (tooltipTrigger === TT_WHEN_PRIMARY && classification === HC_PRIMARY) ||
        (tooltipTrigger === TT_WHEN_RELATED && (classification === HC_PRIMARY || classification === HC_RELATED));

      if (shouldShow) {
        // Get or create tooltip for this element
        let tooltip = elementTooltips.get(element);
        if (!tooltip) {
          tooltip = createTooltipElement();
          elementTooltips.set(element, tooltip);
        }

        showTooltip(tooltip, content);

        // Position based on trigger type
        if (tooltipTrigger === TT_ON_HOVER && event) {
          positionTooltipAtMouse(tooltip, event);
        } else {
          positionTooltipNearElement(tooltip, element);
        }
      } else {
        // Hide tooltip if it exists
        const tooltip = elementTooltips.get(element);
        if (tooltip) {
          hideTooltip(tooltip);
        }
      }
    }
  });
}

/**
 * Clear all highlight classes and tooltips from a group
 * @param {string|null} groupName - Group name
 */
function clearHighlightsInGroup(groupName) {
  const group = getHighlightGroup(groupName);

  group.forEach(entry => {
    ALL_HIGHLIGHT_CLASSES.forEach(cls => entry.element.classList.remove(cls));

    // Hide tooltip if it exists
    const tooltip = elementTooltips.get(entry.element);
    if (tooltip) {
      hideTooltip(tooltip);
    }
  });
}

/**
 * Attach coordinated highlight behavior to an element
 *
 * When this element is hovered, ALL elements in the same group receive
 * highlight classes based on their classifyFn.
 *
 * @param {Element} element - The DOM element to attach to
 * @param {Function} identifyFn - PureScript (datum -> String)
 * @param {Function} classifyFn - PureScript (String -> datum -> Int)
 * @param {string|null} groupName - Optional group name (null for global)
 * @param {Function|null} tooltipContentFn - Optional PureScript (datum -> String) for tooltip content
 * @param {number} tooltipTrigger - When to show tooltip (0=OnHover, 1=WhenPrimary, 2=WhenRelated)
 * @returns {Element} The element (for chaining)
 */
export function attachCoordinatedHighlight_(element) {
  return identifyFn => classifyFn => groupName => tooltipContentFn => tooltipTrigger => () => {
    const group = groupName; // null means global
    const groupKey = group || '_global';

    // Register this element with tooltip config
    // Note: datum may not be set yet, will be read fresh in applyHighlights
    const entry = { element, identifyFn, classifyFn, tooltipContentFn, tooltipTrigger };
    getHighlightGroup(group).push(entry);

    // Attach mouseenter handler
    element.addEventListener('mouseenter', function(event) {
      const d = this.__data__;
      if (!d) return;
      const id = identifyFn(d);
      applyHighlights(group, id, element, event);
    });

    // Attach mouseleave handler
    element.addEventListener('mouseleave', function(event) {
      clearHighlightsInGroup(group);
    });

    return element;
  };
}

/**
 * Clear all highlight classes and tooltips from all groups
 * Also clears the registry (useful for cleanup before re-rendering)
 */
export function clearAllHighlights_() {
  highlightRegistry.forEach((group, key) => {
    group.forEach(entry => {
      ALL_HIGHLIGHT_CLASSES.forEach(cls => entry.element.classList.remove(cls));
    });
  });

  // Hide and remove all tooltips
  elementTooltips.forEach(tooltip => {
    if (tooltip.parentNode) {
      tooltip.parentNode.removeChild(tooltip);
    }
  });
  elementTooltips.clear();

  // Clear registry - elements will re-register on next render
  highlightRegistry.clear();
}

// =============================================================================
// Scroll Utilities
// =============================================================================

/**
 * Scroll to an element by ID with configurable behavior
 * @param {string} elementId - The ID of the element to scroll to
 * @param {string} behavior - Scroll behavior: "smooth", "instant", or "auto"
 * @param {string} block - Vertical alignment: "start", "center", "end", or "nearest"
 * @returns {Effect Unit}
 */
export function scrollToElementById_(elementId) {
  return behavior => block => () => {
    const el = document.getElementById(elementId);
    if (el) {
      el.scrollIntoView({ behavior, block });
    }
  };
}
