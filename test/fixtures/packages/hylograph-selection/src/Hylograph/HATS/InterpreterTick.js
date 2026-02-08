// HATS Tick-Driven Interpreter FFI
// Re-exports from Behavior FFI and native Pointer/Zoom modules

import {
  attachSimpleDrag_ as nativeSimpleDrag,
  attachSimulationDragById_ as nativeSimulationDragById,
  attachSimulationDragNestedById_ as nativeSimulationDragNestedById
} from "../Hylograph.Interaction.Pointer/foreign.js";

import {
  attachZoomNative_
} from "../Hylograph.Interaction.Zoom/foreign.js";

// DOM helpers
export const selectElement = selector => doc => () => {
  return doc.querySelector(selector);
};

// Set attribute on element (handles SVG namespaced attrs and textContent)
export const setAttribute = el => name => value => () => {
  if (name === 'textContent') {
    el.textContent = value;
  } else if (name.startsWith('xlink:')) {
    el.setAttributeNS('http://www.w3.org/1999/xlink', name, value);
  } else if (name.startsWith('xml:')) {
    el.setAttributeNS('http://www.w3.org/XML/1998/namespace', name, value);
  } else {
    el.setAttribute(name, value);
  }
};

// Get attribute from element
export const getAttribute = el => name => () => {
  if (name === 'textContent') {
    return el.textContent || '';
  }
  return el.getAttribute(name) || '';
};

// Bind datum to element (D3-style __data__ property)
export const bindDatum = el => datum => () => {
  el.__data__ = datum;
};

// Set key on element for GUP diffing
export const setKey = el => key => () => {
  el.setAttribute('data-hats-key', key);
};

// Set fold name on element for scoping sibling Folds
export const setFoldName = el => foldName => () => {
  el.setAttribute('data-hats-fold', foldName);
};

// Get key from element
export const getKey = el => () => {
  return el.getAttribute('data-hats-key') || '';
};

// Get direct child elements (for GUP diffing)
export const getChildElements = parent => () => {
  return Array.from(parent.children);
};

// Get direct child elements filtered by tag name (for scoped GUP)
// tagName should be lowercase (e.g., "g", "circle", "path")
export const getChildElementsByTagName = parent => tagName => () => {
  const children = Array.from(parent.children);
  // SVG elements have tagName in lowercase
  return children.filter(el => el.tagName.toLowerCase() === tagName);
};

// Get direct child elements filtered by tag name AND fold name
// This ensures sibling Folds with the same element type don't interfere
export const getChildElementsForFold = parent => tagName => foldName => () => {
  const children = Array.from(parent.children);
  return children.filter(el =>
    el.tagName.toLowerCase() === tagName &&
    el.getAttribute('data-hats-fold') === foldName
  );
};

// Remove element from DOM
export const removeElement = el => () => {
  if (el.parentNode) {
    el.parentNode.removeChild(el);
  }
};

// =============================================================================
// Click handlers
// =============================================================================

export const attachClick = el => handler => () => {
  el.addEventListener('click', function(event) {
    event.stopPropagation();  // Prevent bubbling to parent handlers
    handler();
  });
  el.style.cursor = 'pointer';
};

export const attachClickWithDatum = el => handler => () => {
  el.addEventListener('click', function(event) {
    event.stopPropagation();  // Prevent bubbling to parent handlers
    const d = this.__data__;
    handler(d)();
  });
  el.style.cursor = 'pointer';
};

// =============================================================================
// Mouse event handlers (datum-based - legacy)
// =============================================================================

export const attachMouseEnter = el => handler => () => {
  el.addEventListener('mouseenter', function(event) {
    const d = this.__data__;
    handler(d)();
  });
};

export const attachMouseLeave = el => handler => () => {
  el.addEventListener('mouseleave', function(event) {
    const d = this.__data__;
    handler(d)();
  });
};

export const attachMouseDown = el => handler => () => {
  el.addEventListener('mousedown', function(event) {
    handler();
  });
};

// =============================================================================
// Thunked event handlers (closure-based - new)
// =============================================================================

// Thunked handlers capture their data in closures, so we just invoke the thunk
export const attachMouseEnterThunked = el => handler => () => {
  el.addEventListener('mouseenter', function(event) {
    handler()();  // handler is (Unit -> Effect Unit), invoke with unit then run effect
  });
};

export const attachMouseLeaveThunked = el => handler => () => {
  el.addEventListener('mouseleave', function(event) {
    handler()();
  });
};

export const attachClickThunked = el => handler => () => {
  el.addEventListener('click', function(event) {
    event.stopPropagation();  // Prevent bubbling to parent handlers
    handler()();
  });
  el.style.cursor = 'pointer';
};

// =============================================================================
// Highlight behavior
// =============================================================================

export const attachHighlight = el => enterStyles => leaveStyles => () => {
  el.addEventListener('mouseenter', function(event) {
    enterStyles.forEach(style => {
      this.setAttribute(style.attr, style.value);
    });
  });

  el.addEventListener('mouseleave', function(event) {
    leaveStyles.forEach(style => {
      this.setAttribute(style.attr, style.value);
    });
  });
};

// =============================================================================
// Zoom behavior
// =============================================================================

export const attachZoom = el => scaleMin => scaleMax => targetSelector => () => {
  attachZoomNative_(el)(scaleMin)(scaleMax)(targetSelector)();
};

// =============================================================================
// Drag behaviors
// =============================================================================

export const attachSimpleDrag = el => () => {
  nativeSimpleDrag(el)()();
};

export const attachSimulationDragById = el => simId => () => {
  nativeSimulationDragById(el)(simId)();
};

export const attachSimulationDragNestedById = el => simId => () => {
  nativeSimulationDragNestedById(el)(simId)();
};

// =============================================================================
// Coordinated Highlighting (HATS-specific - thunked)
// =============================================================================

// Global registry for HATS coordinated highlighting
// Key: group name (or "_global" for ungrouped)
// Value: Array of { element, identifyThunk, classifyFn }
const hatsHighlightRegistry = new Map();

// CSS class names (same as BehaviorFFI)
const HIGHLIGHT_PRIMARY = 'highlight-primary';
const HIGHLIGHT_RELATED = 'highlight-related';
const HIGHLIGHT_DIMMED = 'highlight-dimmed';
const HIGHLIGHT_UPSTREAM = 'highlight-upstream';
const HIGHLIGHT_DOWNSTREAM = 'highlight-downstream';
const ALL_HIGHLIGHT_CLASSES = [HIGHLIGHT_PRIMARY, HIGHLIGHT_RELATED, HIGHLIGHT_DIMMED, HIGHLIGHT_UPSTREAM, HIGHLIGHT_DOWNSTREAM];

// HighlightClass enum values (must match PureScript)
const HC_PRIMARY = 0;
const HC_RELATED = 1;
const HC_DIMMED = 2;
const HC_NEUTRAL = 3;
const HC_UPSTREAM = 4;
const HC_DOWNSTREAM = 5;

/**
 * Get or create a highlight group
 */
function getHatsHighlightGroup(groupName) {
  const key = groupName || '_global';
  if (!hatsHighlightRegistry.has(key)) {
    hatsHighlightRegistry.set(key, []);
  }
  return hatsHighlightRegistry.get(key);
}

/**
 * Apply highlight classes to all elements in a group based on hovered id
 */
function applyHatsHighlights(groupName, hoveredId) {
  const group = getHatsHighlightGroup(groupName);

  group.forEach(entry => {
    const { element, classifyFn } = entry;

    // Remove all highlight classes first
    ALL_HIGHLIGHT_CLASSES.forEach(cls => element.classList.remove(cls));

    // Get classification from PureScript thunked function
    // classifyFn is: String -> HighlightClass (Int)
    // It already has datum captured in closure
    const classification = classifyFn(hoveredId);

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
  });
}

/**
 * Clear all highlight classes from a group
 */
function clearHatsHighlightsInGroup(groupName) {
  const group = getHatsHighlightGroup(groupName);
  group.forEach(entry => {
    ALL_HIGHLIGHT_CLASSES.forEach(cls => entry.element.classList.remove(cls));
  });
}

// =============================================================================
// HATS Tooltip Support
// =============================================================================

// TooltipTrigger enum values (must match PureScript TooltipTrigger in Behavior.Types)
const TT_ON_HOVER = 0;
const TT_WHEN_PRIMARY = 1;
const TT_WHEN_RELATED = 2;

// Container for HATS tooltips
let hatsTooltipContainer = null;
// Map of element -> tooltip div
const hatsElementTooltips = new Map();

function getHatsTooltipContainer() {
  if (!hatsTooltipContainer) {
    hatsTooltipContainer = document.createElement('div');
    hatsTooltipContainer.className = 'hats-tooltip-container';
    hatsTooltipContainer.style.cssText = 'position: fixed; top: 0; left: 0; pointer-events: none; z-index: 10000;';
    document.body.appendChild(hatsTooltipContainer);
  }
  return hatsTooltipContainer;
}

function createHatsTooltip() {
  const tooltip = document.createElement('div');
  tooltip.className = 'hats-tooltip';
  tooltip.style.cssText = `
    position: absolute;
    background: rgba(45, 45, 45, 0.85);
    color: #f0f0f0;
    padding: 10px 16px;
    font-size: 13px;
    font-weight: 500;
    font-family: 'Courier New', Courier, monospace;
    white-space: pre-line;
    pointer-events: none;
    opacity: 0;
    transition: opacity 0.15s ease-in-out;
    box-shadow: 0 4px 12px rgba(0, 0, 0, 0.3);
    border: none;
    border-radius: 4px;
    min-width: 280px;
    max-width: 480px;
    line-height: 1.6;
    backdrop-filter: blur(8px);
    -webkit-backdrop-filter: blur(8px);
  `;
  getHatsTooltipContainer().appendChild(tooltip);
  return tooltip;
}

function positionHatsTooltip(tooltip, event) {
  const x = event.clientX + 15;
  const y = event.clientY - 10;
  tooltip.style.left = `${x}px`;
  tooltip.style.top = `${y}px`;
}

function showHatsTooltip(tooltip, content) {
  tooltip.textContent = content;
  tooltip.style.opacity = '1';
}

function hideHatsTooltip(tooltip) {
  if (tooltip) {
    tooltip.style.opacity = '0';
  }
}

/**
 * Attach HATS coordinated highlight behavior to an element
 *
 * Uses thunked functions that have datum captured in closures.
 *
 * @param {Element} element - The DOM element to attach to
 * @param {Function} identifyThunk - PureScript (Unit -> String), returns this element's identity
 * @param {Function} classifyFn - PureScript (String -> Int), takes hoveredId, returns HighlightClass
 * @param {string|null} groupName - Optional group name (null for global)
 * @param {Function|null} tooltipContentThunk - Optional PureScript (Unit -> String), returns tooltip content
 * @param {number} tooltipTrigger - When to show tooltip (0=OnHover, 1=WhenPrimary, 2=WhenRelated)
 * @returns {Effect Unit}
 */
export const attachCoordinatedHighlightThunked = element => identifyThunk => classifyFn => groupName => tooltipContentThunk => tooltipTrigger => () => {
  const group = groupName; // null means global

  // Register this element with tooltip info
  const entry = { element, identifyThunk, classifyFn, tooltipContentThunk, tooltipTrigger };
  getHatsHighlightGroup(group).push(entry);

  // Attach mouseenter handler
  element.addEventListener('mouseenter', function(event) {
    // Get identity by invoking the thunk (datum is captured in closure)
    const hoveredId = identifyThunk();
    applyHatsHighlightsWithTooltips(group, hoveredId, element, event);
  });

  // Attach mouseleave handler
  element.addEventListener('mouseleave', function(event) {
    clearHatsHighlightsInGroupWithTooltips(group);
  });
};

/**
 * Apply highlights and tooltips to all elements in a group
 */
function applyHatsHighlightsWithTooltips(groupName, hoveredId, triggerElement, event) {
  const group = getHatsHighlightGroup(groupName);

  group.forEach(entry => {
    const { element, classifyFn, tooltipContentThunk, tooltipTrigger } = entry;

    // Remove all highlight classes first
    ALL_HIGHLIGHT_CLASSES.forEach(cls => element.classList.remove(cls));

    // Apply classification
    const classification = classifyFn(hoveredId);
    switch (classification) {
      case HC_PRIMARY:
        element.classList.add('highlight-primary');
        break;
      case HC_RELATED:
        element.classList.add('highlight-related');
        break;
      case HC_UPSTREAM:
        element.classList.add('highlight-upstream');
        break;
      case HC_DOWNSTREAM:
        element.classList.add('highlight-downstream');
        break;
      case HC_DIMMED:
        element.classList.add('highlight-dimmed');
        break;
      case HC_NEUTRAL:
      default:
        // No class applied
        break;
    }

    // Handle tooltips if configured
    if (tooltipContentThunk) {
      const shouldShow =
        (tooltipTrigger === TT_ON_HOVER && element === triggerElement) ||
        (tooltipTrigger === TT_WHEN_PRIMARY && classification === HC_PRIMARY) ||
        (tooltipTrigger === TT_WHEN_RELATED && (classification === HC_PRIMARY || classification === HC_RELATED));

      if (shouldShow) {
        // Get or create tooltip for this element
        let tooltip = hatsElementTooltips.get(element);
        if (!tooltip) {
          tooltip = createHatsTooltip();
          hatsElementTooltips.set(element, tooltip);
        }

        // Get content by invoking the thunk
        const content = tooltipContentThunk();
        showHatsTooltip(tooltip, content);

        // Position at mouse for OnHover
        if (tooltipTrigger === TT_ON_HOVER && event) {
          positionHatsTooltip(tooltip, event);
        }
      } else {
        // Hide tooltip if it exists
        const tooltip = hatsElementTooltips.get(element);
        if (tooltip) {
          hideHatsTooltip(tooltip);
        }
      }
    }
  });
}

/**
 * Clear highlights and tooltips from a group
 */
function clearHatsHighlightsInGroupWithTooltips(groupName) {
  const group = getHatsHighlightGroup(groupName);
  group.forEach(entry => {
    ALL_HIGHLIGHT_CLASSES.forEach(cls => entry.element.classList.remove(cls));

    // Hide tooltip if it exists
    const tooltip = hatsElementTooltips.get(entry.element);
    if (tooltip) {
      hideHatsTooltip(tooltip);
    }
  });
}

/**
 * Clear all HATS coordinated highlights (useful before re-rendering)
 */
export const clearAllHatsHighlights = () => {
  hatsHighlightRegistry.forEach((group, key) => {
    group.forEach(entry => {
      ALL_HIGHLIGHT_CLASSES.forEach(cls => entry.element.classList.remove(cls));
    });
  });
  hatsHighlightRegistry.clear();
};

// =============================================================================
// Coordinated Interaction (supports brush + hover + selection)
// =============================================================================

// This integrates with the full Coordinated framework which handles:
// - HoverTrigger: element identity hovered
// - BrushTrigger: bounding box selection
// - SelectionTrigger: discrete ID set
// - FocusTrigger: single focused element
// - ClearTrigger: reset all interaction state

// Global registry for coordinated interaction elements
// Key: group name (or "_global" for ungrouped)
// Value: Array of { element, identifyThunk, respondFn, positionThunk }
const coordInteractionRegistry = new Map();

// InteractionState enum values (must match PureScript Coordinated module)
const IS_PRIMARY = 0;
const IS_RELATED = 1;
const IS_SELECTED = 2;
const IS_DIMMED = 3;
const IS_NEUTRAL = 4;

// CSS class names for coordinated interaction
const COORD_PRIMARY = 'coord-primary';
const COORD_RELATED = 'coord-related';
const COORD_SELECTED = 'coord-selected';
const COORD_DIMMED = 'coord-dimmed';
const ALL_COORD_CLASSES = [COORD_PRIMARY, COORD_RELATED, COORD_SELECTED, COORD_DIMMED];

function getCoordInteractionGroup(groupName) {
  const key = groupName || '_global';
  if (!coordInteractionRegistry.has(key)) {
    coordInteractionRegistry.set(key, []);
  }
  return coordInteractionRegistry.get(key);
}

/**
 * Apply state CSS class to an element based on InteractionState int value
 */
function applyStateClass(element, state) {
  // Remove all coord classes first
  ALL_COORD_CLASSES.forEach(cls => element.classList.remove(cls));

  // Apply appropriate class
  switch (state) {
    case IS_PRIMARY:
      element.classList.add(COORD_PRIMARY);
      break;
    case IS_RELATED:
      element.classList.add(COORD_RELATED);
      break;
    case IS_SELECTED:
      element.classList.add(COORD_SELECTED);
      break;
    case IS_DIMMED:
      element.classList.add(COORD_DIMMED);
      break;
    case IS_NEUTRAL:
    default:
      // No class applied
      break;
  }
}

/**
 * Apply hover interaction to all elements in a group
 * @param {string|null} groupName - Group name
 * @param {string} hoveredId - The ID of the hovered element
 */
function applyHoverInteraction(groupName, hoveredId) {
  const group = getCoordInteractionGroup(groupName);
  group.forEach(entry => {
    const state = entry.respondToHover(hoveredId);
    applyStateClass(entry.element, state);
  });
}

/**
 * Apply brush interaction to all elements in a group
 * Uses semantic selection: identifies points in box, then highlights all points with same IDs
 * @param {string|null} groupName - Group name
 * @param {object} box - { x0, y0, x1, y1 } bounding box
 * @param {Element} sourceCell - The cell where the brush originated (for position checking)
 */
function applyBrushInteraction(groupName, box, sourceCell) {
  const group = getCoordInteractionGroup(groupName);

  // First pass: collect IDs of elements whose positions are in the box
  // Only check elements in the same cell (same parent)
  const selectedIds = new Set();
  group.forEach(entry => {
    if (entry.getPosition) {
      const pos = entry.getPosition();
      // Check if this element is in the source cell
      const elementCell = entry.element.closest('g[id^="cell-"]');
      if (elementCell === sourceCell) {
        // Check if position is in box
        if (pos.x >= box.x0 && pos.x <= box.x1 && pos.y >= box.y0 && pos.y <= box.y1) {
          const id = entry.identifyThunk();
          selectedIds.add(id);
        }
      }
    }
  });

  // Second pass: highlight elements based on whether their ID is in the selected set
  group.forEach(entry => {
    const id = entry.identifyThunk();
    let state;
    if (selectedIds.size === 0) {
      state = IS_NEUTRAL;
    } else if (selectedIds.has(id)) {
      state = IS_SELECTED;
    } else {
      state = IS_DIMMED;
    }
    applyStateClass(entry.element, state);
  });
}

/**
 * Apply clear interaction to all elements in a group
 * @param {string|null} groupName - Group name
 */
function applyClearInteraction(groupName) {
  const group = getCoordInteractionGroup(groupName);
  group.forEach(entry => {
    const state = entry.respondToClear();
    applyStateClass(entry.element, state);
  });
}

/**
 * Attach coordinated interaction behavior to an element
 *
 * This registers the element to respond to interaction triggers.
 * Each trigger type has its own respond function that takes raw data
 * and returns an InteractionState (as Int).
 *
 * @param {Element} element - The DOM element
 * @param {Function} identifyThunk - (Unit -> String), returns element identity
 * @param {Function} respondToHover - (String -> Int), hoveredId -> state
 * @param {Function} respondToBrush - (BoundingBox -> Int), box -> state
 * @param {Function} respondToClear - (Unit -> Int), _ -> state
 * @param {object|null} positionThunk - Maybe (Unit -> {x, y}), for brush hit-testing
 * @param {string|null} groupName - Group name
 */
export const attachCoordinatedInteractionThunked = element => identifyThunk => respondToHover => respondToBrush => respondToClear => positionThunk => groupName => () => {
  const group = groupName; // null means global

  // Extract position thunk if present (Maybe is encoded as { value0: fn } or null/undefined)
  const getPosition = positionThunk && positionThunk.value0 ? positionThunk.value0 : null;

  // Register this element with separate respond functions
  const entry = { element, identifyThunk, respondToHover, respondToBrush, respondToClear, getPosition };
  getCoordInteractionGroup(group).push(entry);

  // Attach mouseenter handler
  element.addEventListener('mouseenter', function(event) {
    const hoveredId = identifyThunk();
    applyHoverInteraction(group, hoveredId);
  });

  // Attach mouseleave handler
  element.addEventListener('mouseleave', function(event) {
    applyClearInteraction(group);
  });
};

// =============================================================================
// Coordinated Brush (emits triggers to coordinated interaction elements)
// =============================================================================

// Store active brush handles for cleanup
const activeBrushes = new Map();

/**
 * Attach a coordinated brush to an element
 *
 * When the user brushes on this element, BrushTrigger is emitted to all
 * elements registered with attachCoordinatedInteractionThunked in the same group.
 *
 * @param {Element} element - The SVG element to attach brush to
 * @param {object} extent - { x0, y0, x1, y1 } brushable area
 * @param {string|null} groupName - Group name
 */
export const attachCoordinatedBrushThunked = element => extent => groupName => () => {
  const group = groupName;

  // Find the brush-background rect after HATS creates it
  // Use a MutationObserver to wait for it, or find it lazily on first interaction
  let brushRect = null;

  function getBrushRect() {
    if (!brushRect) {
      brushRect = element.querySelector('.brush-background');
      if (brushRect) {
        // Style it for brush selection feedback
        brushRect.style.fill = 'transparent';
        brushRect.style.stroke = 'transparent';
        brushRect.style.strokeWidth = '1';
      }
    }
    return brushRect;
  }

  // Create a separate overlay rect for the selection visualization
  // Append it to the PARENT (cell group) to avoid index collision
  const ns = 'http://www.w3.org/2000/svg';
  const selectionRect = document.createElementNS(ns, 'rect');
  selectionRect.setAttribute('class', 'brush-selection-overlay');
  selectionRect.setAttribute('fill', 'rgba(100, 100, 200, 0.2)');
  selectionRect.setAttribute('stroke', '#6666cc');
  selectionRect.setAttribute('stroke-width', '1');
  selectionRect.setAttribute('visibility', 'hidden');
  selectionRect.setAttribute('pointer-events', 'none');
  // Append to parent (cell group) so it's on top of circles
  const cellGroup = element.parentElement;
  if (cellGroup) {
    cellGroup.appendChild(selectionRect);
  }

  let isDragging = false;
  let startX = 0;
  let startY = 0;

  // Throttle state for brush callbacks (150ms = ~7fps - necessary for large datasets)
  let lastBrushTime = 0;
  let pendingBrushFrame = null;
  const BRUSH_THROTTLE_MS = 150;

  // Get element-local coordinates from event
  // Uses the parent's CTM to account for transforms (important for SPLOM cells)
  function getLocalCoords(event) {
    const svg = element.closest('svg');
    if (!svg) return { x: event.clientX, y: event.clientY };

    const pt = svg.createSVGPoint();
    pt.x = event.clientX;
    pt.y = event.clientY;

    // Use parent's CTM (the cell group with transform) instead of root SVG
    // This gives us coordinates in the local cell space
    const parent = element.parentElement;
    const ctm = parent && parent.getScreenCTM ? parent.getScreenCTM() : svg.getScreenCTM();
    if (!ctm) return { x: event.clientX, y: event.clientY };

    const localP = pt.matrixTransform(ctm.inverse());
    return { x: localP.x, y: localP.y };
  }

  element.addEventListener('pointerdown', function(event) {
    // Only respond to primary button
    if (event.button !== 0) return;

    // Check if clicking on brush-background or the group itself
    const rect = getBrushRect();
    if (event.target !== element && event.target !== rect) return;

    isDragging = true;
    const coords = getLocalCoords(event);
    startX = Math.max(extent.x0, Math.min(extent.x1, coords.x));
    startY = Math.max(extent.y0, Math.min(extent.y1, coords.y));

    selectionRect.setAttribute('x', startX);
    selectionRect.setAttribute('y', startY);
    selectionRect.setAttribute('width', 0);
    selectionRect.setAttribute('height', 0);
    selectionRect.setAttribute('visibility', 'visible');

    element.setPointerCapture(event.pointerId);
    event.preventDefault();
  });

  element.addEventListener('pointermove', function(event) {
    if (!isDragging) return;

    const coords = getLocalCoords(event);
    const currentX = Math.max(extent.x0, Math.min(extent.x1, coords.x));
    const currentY = Math.max(extent.y0, Math.min(extent.y1, coords.y));

    const x = Math.min(startX, currentX);
    const y = Math.min(startY, currentY);
    const width = Math.abs(currentX - startX);
    const height = Math.abs(currentY - startY);

    selectionRect.setAttribute('x', x);
    selectionRect.setAttribute('y', y);
    selectionRect.setAttribute('width', width);
    selectionRect.setAttribute('height', height);

    // Emit brush interaction with the box (THROTTLED to prevent runaway)
    // Pass the source cell so we only check positions within that cell
    const box = { x0: x, y0: y, x1: x + width, y1: y + height };
    const sourceCell = element.closest('g[id^="cell-"]');

    const now = performance.now();
    if (now - lastBrushTime >= BRUSH_THROTTLE_MS) {
      lastBrushTime = now;
      if (pendingBrushFrame) {
        cancelAnimationFrame(pendingBrushFrame);
        pendingBrushFrame = null;
      }
      applyBrushInteraction(group, box, sourceCell);
    } else if (!pendingBrushFrame) {
      // Schedule trailing call to ensure final position is processed
      pendingBrushFrame = requestAnimationFrame(() => {
        pendingBrushFrame = null;
        lastBrushTime = performance.now();
        applyBrushInteraction(group, box, sourceCell);
      });
    }
  });

  element.addEventListener('pointerup', function(event) {
    if (!isDragging) return;
    isDragging = false;
    element.releasePointerCapture(event.pointerId);
  });

  // Click to clear (when not dragging)
  element.addEventListener('click', function(event) {
    const rect = getBrushRect();
    if (event.target !== element && event.target !== rect) return;

    // Hide selection rect
    selectionRect.setAttribute('visibility', 'hidden');

    // Emit clear interaction
    applyClearInteraction(group);
  });

  // Store handle for potential cleanup
  const handle = { element, selectionRect, group };
  if (!activeBrushes.has(group)) {
    activeBrushes.set(group, []);
  }
  activeBrushes.get(group).push(handle);
};
