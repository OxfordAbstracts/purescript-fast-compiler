// RequestAnimationFrame FFI
// Provides browser animation frame timing for the TickCoordinator

export const requestAnimationFrame_ = function(callback) {
  return function() {
    return window.requestAnimationFrame(function(timestamp) {
      callback(timestamp)();
    });
  };
};

export const cancelAnimationFrame_ = function(id) {
  return function() {
    window.cancelAnimationFrame(id);
  };
};

export const performanceNow_ = function() {
  return performance.now();
};
