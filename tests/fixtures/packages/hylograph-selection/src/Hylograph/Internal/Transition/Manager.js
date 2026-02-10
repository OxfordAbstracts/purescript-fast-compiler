// FFI for PSD3.Internal.Transition.Manager

// Math functions
export const pow = x => y => Math.pow(x, y);
export const sin = x => Math.sin(x);
export const cos = x => Math.cos(x);
export const sqrt = x => Math.sqrt(x);

// Set an attribute on a DOM element
export const setAttribute = element => name => value => () => {
  element.setAttribute(name, value);
};

// Read a numeric attribute from an element
// Returns 0.0 if the attribute doesn't exist or isn't parseable
export const readAttributeNumber = element => name => () => {
  const raw = element.getAttribute(name);
  if (raw === null) return 0.0;
  const parsed = parseFloat(raw);
  return isNaN(parsed) ? 0.0 : parsed;
};

// WeakMap to store unique IDs for elements
const elementIdMap = new WeakMap();
let nextElementId = 0;

// Get a unique reference string for an element
// Uses a WeakMap to generate stable IDs without leaking memory
export const unsafeElementRef = element => {
  let id = elementIdMap.get(element);
  if (id === undefined) {
    id = `__elem_${nextElementId++}`;
    elementIdMap.set(element, id);
  }
  return id;
};
