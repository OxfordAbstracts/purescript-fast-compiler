// HATS Transitions FFI
// DOM operations for tick-driven transitions

// Set attribute on element (handles textContent specially)
export const setAttribute = el => name => value => () => {
  if (name === 'textContent') {
    el.textContent = value;
  } else if (name.startsWith('xlink:')) {
    el.setAttributeNS('http://www.w3.org/1999/xlink', name, value);
  } else {
    el.setAttribute(name, value);
  }
};

// Remove element from DOM
export const removeElement = el => () => {
  if (el.parentNode) {
    el.parentNode.removeChild(el);
  }
};
