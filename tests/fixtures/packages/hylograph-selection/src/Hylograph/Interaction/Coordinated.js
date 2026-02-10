// Coordinated Interaction Framework - Native Implementation
// Handles registration, trigger dispatch, and CSS class management

// =============================================================================
// Registry
// =============================================================================

// Global registry of coordinated elements
// Key: group name (or "_global")
// Value: Array of { element, config }
const registry = new Map();

// CSS class names
const CSS_CLASSES = {
  primary: 'coord-primary',
  related: 'coord-related',
  selected: 'coord-selected',
  dimmed: 'coord-dimmed'
};

// InteractionState enum values (must match PureScript)
const STATE = {
  PRIMARY: 0,
  RELATED: 1,
  SELECTED: 2,
  DIMMED: 3,
  NEUTRAL: 4
};

// =============================================================================
// Internal Helpers
// =============================================================================

function getGroup(groupName) {
  const key = groupName || '_global';
  if (!registry.has(key)) {
    registry.set(key, []);
  }
  return registry.get(key);
}

function clearAllClasses(element) {
  Object.values(CSS_CLASSES).forEach(cls => {
    element.classList.remove(cls);
  });
}

function applyState(element, state) {
  clearAllClasses(element);
  switch (state) {
    case STATE.PRIMARY:
      element.classList.add(CSS_CLASSES.primary);
      break;
    case STATE.RELATED:
      element.classList.add(CSS_CLASSES.related);
      break;
    case STATE.SELECTED:
      element.classList.add(CSS_CLASSES.selected);
      break;
    case STATE.DIMMED:
      element.classList.add(CSS_CLASSES.dimmed);
      break;
    case STATE.NEUTRAL:
    default:
      // No class
      break;
  }
}

// =============================================================================
// Trigger Dispatch
// =============================================================================

/**
 * Dispatch a trigger to all elements in a group
 * Each element's respond function is called to determine its state
 */
function dispatchTrigger(groupName, trigger) {
  const group = getGroup(groupName);

  group.forEach(entry => {
    const { element, respondFn } = entry;
    const datum = element.__data__;

    if (!datum) {
      console.warn('[Coordinated] No datum on element', element);
      return;
    }

    // Call PureScript respond function: trigger -> datum -> Int (state)
    const state = respondFn(trigger)(datum);
    applyState(element, state);
  });
}

/**
 * Clear all interaction state in a group
 */
function clearGroup(groupName) {
  const group = getGroup(groupName);
  group.forEach(entry => {
    clearAllClasses(entry.element);
  });
}

// =============================================================================
// Trigger Constructors (for use from JavaScript)
// =============================================================================

// These create PureScript-compatible trigger objects

function hoverTrigger(id) {
  // HoverTrigger String
  return { tag: 'HoverTrigger', value0: id };
}

function brushTrigger(box) {
  // BrushTrigger BoundingBox
  return { tag: 'BrushTrigger', value0: box };
}

function selectionTrigger(ids) {
  // SelectionTrigger (Set String)
  // Note: PureScript Set is different from JS Set, handle conversion
  return { tag: 'SelectionTrigger', value0: ids };
}

function focusTrigger(maybeId) {
  // FocusTrigger (Maybe String)
  return { tag: 'FocusTrigger', value0: maybeId };
}

function clearTrigger() {
  return { tag: 'ClearTrigger' };
}

// =============================================================================
// FFI Exports
// =============================================================================

/**
 * Register an element for coordinated interactions
 *
 * @param {Element} element - DOM element to register
 * @param {Function} identifyFn - datum -> String
 * @param {Function} respondFn - trigger -> datum -> Int (InteractionState)
 * @param {String|null} groupName - Group name or null for global
 * @returns {Effect (Effect Unit)} - Returns unregister function
 */
export function registerCoordinated_(element) {
  return identifyFn => respondFn => groupName => () => {
    const group = getGroup(groupName);

    const entry = {
      element,
      identifyFn,
      respondFn
    };

    group.push(entry);

    // Set up hover listeners on this element
    element.addEventListener('mouseenter', handleMouseEnter);
    element.addEventListener('mouseleave', handleMouseLeave);

    function handleMouseEnter() {
      const datum = element.__data__;
      if (!datum) return;
      const id = identifyFn(datum);
      dispatchTrigger(groupName, hoverTrigger(id));
    }

    function handleMouseLeave() {
      dispatchTrigger(groupName, clearTrigger());
    }

    // Return unregister function
    return () => {
      element.removeEventListener('mouseenter', handleMouseEnter);
      element.removeEventListener('mouseleave', handleMouseLeave);

      const idx = group.indexOf(entry);
      if (idx !== -1) {
        group.splice(idx, 1);
      }

      clearAllClasses(element);
    };
  };
}

/**
 * Emit a trigger to a group (for programmatic triggering)
 * Used by brush handlers to dispatch brush regions
 */
export function emitTrigger_(groupName) {
  return trigger => () => {
    dispatchTrigger(groupName, trigger);
  };
}

/**
 * Clear all interaction state in a group
 */
export function clearInteractions_(groupName) {
  return () => {
    clearGroup(groupName);
  };
}

/**
 * Create a HoverTrigger
 */
export function mkHoverTrigger_(id) {
  return hoverTrigger(id);
}

/**
 * Create a BrushTrigger
 */
export function mkBrushTrigger_(box) {
  return brushTrigger(box);
}

/**
 * Create a ClearTrigger
 */
export function mkClearTrigger_() {
  return clearTrigger();
}

/**
 * Create a FocusTrigger
 */
export function mkFocusTrigger_(maybeId) {
  return focusTrigger(maybeId);
}
