// Simulation.js - Animation loop FFI for WASM kernel

// Request animation frame with cancellation support
export const requestAnimationFrame_ = (callback) => () => {
  return window.requestAnimationFrame(() => callback());
};

export const cancelAnimationFrame_ = (id) => () => {
  window.cancelAnimationFrame(id);
};
