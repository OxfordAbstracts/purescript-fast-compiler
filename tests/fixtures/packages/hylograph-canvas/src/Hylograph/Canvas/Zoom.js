// PSD3.Canvas.Zoom - Zoom and pan event handling

// Subscribe to wheel events for zooming
export function subscribeWheel_(canvas) {
  return function(callback) {
    return function() {
      const handler = function(e) {
        e.preventDefault();

        // Calculate zoom factor
        // Normalize across browsers (some use deltaY in pixels, some in lines)
        const normalizedDelta = e.deltaY > 0 ? -1 : 1;
        const delta = Math.pow(1.1, normalizedDelta);  // 1.1 for zoom in, ~0.91 for zoom out

        // Get mouse position relative to canvas
        const rect = canvas.getBoundingClientRect();
        const x = e.clientX - rect.left;
        const y = e.clientY - rect.top;

        callback({ delta: delta, x: x, y: y })();
      };

      canvas.addEventListener('wheel', handler, { passive: false });

      // Return unsubscribe function
      return function() {
        canvas.removeEventListener('wheel', handler);
      };
    };
  };
}

// Subscribe to drag events for panning
export function subscribeDrag_(canvas) {
  return function(callback) {
    return function() {
      let dragging = false;
      let lastX = 0;
      let lastY = 0;

      const mouseDown = function(e) {
        // Only handle left mouse button or touch
        if (e.button !== 0 && e.type !== 'touchstart') return;

        dragging = true;

        if (e.type === 'touchstart') {
          lastX = e.touches[0].clientX;
          lastY = e.touches[0].clientY;
        } else {
          lastX = e.clientX;
          lastY = e.clientY;
        }

        e.preventDefault();
      };

      const mouseMove = function(e) {
        if (!dragging) return;

        let currentX, currentY;
        if (e.type === 'touchmove') {
          currentX = e.touches[0].clientX;
          currentY = e.touches[0].clientY;
        } else {
          currentX = e.clientX;
          currentY = e.clientY;
        }

        const dx = currentX - lastX;
        const dy = currentY - lastY;

        lastX = currentX;
        lastY = currentY;

        callback({ dx: dx, dy: dy })();

        e.preventDefault();
      };

      const mouseUp = function(e) {
        dragging = false;
      };

      // Mouse events
      canvas.addEventListener('mousedown', mouseDown);
      window.addEventListener('mousemove', mouseMove);
      window.addEventListener('mouseup', mouseUp);

      // Touch events for mobile
      canvas.addEventListener('touchstart', mouseDown, { passive: false });
      window.addEventListener('touchmove', mouseMove, { passive: false });
      window.addEventListener('touchend', mouseUp);

      // Return unsubscribe function
      return function() {
        canvas.removeEventListener('mousedown', mouseDown);
        window.removeEventListener('mousemove', mouseMove);
        window.removeEventListener('mouseup', mouseUp);
        canvas.removeEventListener('touchstart', mouseDown);
        window.removeEventListener('touchmove', mouseMove);
        window.removeEventListener('touchend', mouseUp);
      };
    };
  };
}
