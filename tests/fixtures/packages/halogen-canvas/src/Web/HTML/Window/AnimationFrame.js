export function requestAnimationFrame(fn) {
  return function(window) {
    return function() {
      return window.requestAnimationFrame(t => fn(t)());
    };
  };
}

