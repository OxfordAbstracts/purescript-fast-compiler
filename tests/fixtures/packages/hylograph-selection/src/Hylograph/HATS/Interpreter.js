// HATS Interpreter FFI
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
    // textContent is a property, not an attribute
    el.textContent = value;
  } else if (name.startsWith('xlink:')) {
    el.setAttributeNS('http://www.w3.org/1999/xlink', name, value);
  } else if (name.startsWith('xml:')) {
    el.setAttributeNS('http://www.w3.org/XML/1998/namespace', name, value);
  } else {
    el.setAttribute(name, value);
  }
};

// Bind datum to element (D3-style __data__ property)
export const bindDatum = el => datum => () => {
  el.__data__ = datum;
};

// Get datum from element
export const getDatum = el => () => {
  return el.__data__;
};

// =============================================================================
// GUP (General Update Pattern) helpers
// =============================================================================

// Set key on element for GUP diffing
export const setKey = el => key => () => {
  el.setAttribute('data-hats-key', key);
};

// Get key from element
export const getKey = el => () => {
  return el.getAttribute('data-hats-key') || '';
};

// Set fold name on element for scoping sibling Folds
export const setFoldName = el => foldName => () => {
  el.setAttribute('data-hats-fold', foldName);
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

// Remove element from DOM after a delay (for exit transitions)
export const removeElementDelayed = el => delayMs => () => {
  setTimeout(() => {
    if (el.parentNode) {
      el.parentNode.removeChild(el);
    }
  }, delayMs);
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
// Mouse event handlers
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
// Highlight behavior
// =============================================================================

export const attachHighlight = el => enterStyles => leaveStyles => () => {
  el.addEventListener('mouseenter', function(event) {
    // Apply enter styles
    enterStyles.forEach(style => {
      this.setAttribute(style.attr, style.value);
    });
  });

  el.addEventListener('mouseleave', function(event) {
    // Apply leave styles
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
