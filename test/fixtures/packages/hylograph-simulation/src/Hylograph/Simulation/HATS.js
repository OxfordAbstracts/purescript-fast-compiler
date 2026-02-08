// PSD3.Simulation.HATS FFI
//
// Fast DOM updates for simulation tick - only updates transform attribute.
// Uses vanilla DOM (no D3 dependency) for maximum performance.

/**
 * Update transform attribute on all node elements.
 *
 * Finds elements by data-id attribute and sets transform to translate(x,y).
 * This is much faster than rebuilding the HATS tree at 60fps.
 *
 * @param {string} containerSelector - CSS selector for container element
 * @param {Array} nodes - Array of nodes with {id, x, y, ...}
 * @returns {function} Effect thunk
 */
export const updateNodeTransformsFFI = containerSelector => nodes => () => {
  const container = document.querySelector(containerSelector);
  if (!container) {
    // Container might not exist yet during initialization
    return;
  }

  // Build a map of id -> {x, y} for O(1) lookups
  const positionMap = new Map();
  for (const node of nodes) {
    positionMap.set(String(node.id), { x: node.x, y: node.y });
  }

  // Find all elements with data-id attribute and update their transforms
  const elements = container.querySelectorAll('[data-id]');
  for (const el of elements) {
    const id = el.getAttribute('data-id');
    const pos = positionMap.get(id);
    if (pos) {
      el.setAttribute('transform', `translate(${pos.x},${pos.y})`);
    }
  }
};

/**
 * Update transform and radius on all node elements.
 *
 * Like updateNodeTransformsFFI but also updates radius on child circles.
 *
 * @param {string} containerSelector - CSS selector for container element
 * @param {Array} nodes - Array of nodes with {id, x, y, r, ...}
 * @returns {function} Effect thunk
 */
export const updateNodeTransformsWithRadiusFFI = containerSelector => nodes => () => {
  const container = document.querySelector(containerSelector);
  if (!container) {
    return;
  }

  // Build a map of id -> {x, y, r} for O(1) lookups
  const positionMap = new Map();
  for (const node of nodes) {
    positionMap.set(String(node.id), { x: node.x, y: node.y, r: node.r });
  }

  // Find all elements with data-id attribute and update their transforms
  const elements = container.querySelectorAll('[data-id]');
  for (const el of elements) {
    const id = el.getAttribute('data-id');
    const pos = positionMap.get(id);
    if (pos) {
      el.setAttribute('transform', `translate(${pos.x},${pos.y})`);

      // Update radius on first circle child (common pattern)
      const circle = el.querySelector('circle');
      if (circle && pos.r !== undefined) {
        circle.setAttribute('r', String(pos.r));
      }
    }
  }
};
