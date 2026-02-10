// PSD3.Canvas - High-performance Canvas rendering for PSD3 visualizations

// CanvasContext stores all rendering state
function makeContext(canvas, config) {
  return {
    canvas: canvas,
    ctx: canvas.getContext('2d'),
    width: config.width,
    height: config.height,
    centerOrigin: config.centerOrigin,
    transform: { scale: 1.0, translateX: 0.0, translateY: 0.0 }
  };
}

// Create a Canvas element in the given container
export function createCanvas_(containerSelector) {
  return function(config) {
    return function() {
      const container = document.querySelector(containerSelector);
      if (!container) {
        throw new Error('Canvas container not found: ' + containerSelector);
      }

      // Clear container
      container.innerHTML = '';

      // Create canvas element
      const canvas = document.createElement('canvas');
      canvas.width = config.width;
      canvas.height = config.height;
      canvas.style.width = '100%';
      canvas.style.maxWidth = config.width + 'px';
      canvas.style.height = 'auto';
      canvas.style.background = config.background;
      canvas.style.borderRadius = '4px';

      container.appendChild(canvas);

      return makeContext(canvas, config);
    };
  };
}

// Clear the canvas
export function clearCanvas_(context) {
  return function() {
    const ctx = context.ctx;
    ctx.save();
    ctx.setTransform(1, 0, 0, 1, 0, 0);
    ctx.clearRect(0, 0, context.width, context.height);
    ctx.restore();
  };
}

// Get the canvas DOM element
export function getCanvasElement_(context) {
  return function() {
    return context.canvas;
  };
}

// Set the transform
export function setTransform_(context) {
  return function(transform) {
    return function() {
      context.transform = transform;
    };
  };
}

// Reset transform to identity
export function resetTransform_(context) {
  return function() {
    context.transform = { scale: 1.0, translateX: 0.0, translateY: 0.0 };
  };
}

// Apply current transform to canvas context
function applyContextTransform(context) {
  const ctx = context.ctx;
  const t = context.transform;

  // Start from identity
  ctx.setTransform(1, 0, 0, 1, 0, 0);

  // Apply center offset if enabled
  if (context.centerOrigin) {
    ctx.translate(context.width / 2, context.height / 2);
  }

  // Apply zoom/pan transform
  ctx.translate(t.translateX, t.translateY);
  ctx.scale(t.scale, t.scale);
}

// Draw a single circle
export function drawCircle_(context) {
  return function(spec) {
    return function() {
      const ctx = context.ctx;

      ctx.save();
      applyContextTransform(context);

      ctx.beginPath();
      ctx.arc(spec.x, spec.y, spec.radius, 0, Math.PI * 2);
      ctx.globalAlpha = spec.opacity;
      ctx.fillStyle = spec.fill;
      ctx.fill();

      if (spec.strokeWidth > 0) {
        ctx.strokeStyle = spec.stroke;
        ctx.lineWidth = spec.strokeWidth;
        ctx.stroke();
      }

      ctx.globalAlpha = 1;
      ctx.restore();
    };
  };
}

// Draw a single line
export function drawLine_(context) {
  return function(spec) {
    return function() {
      const ctx = context.ctx;

      ctx.save();
      applyContextTransform(context);

      ctx.beginPath();
      ctx.moveTo(spec.x1, spec.y1);
      ctx.lineTo(spec.x2, spec.y2);
      ctx.globalAlpha = spec.opacity;
      ctx.strokeStyle = spec.stroke;
      ctx.lineWidth = spec.strokeWidth;
      ctx.stroke();

      ctx.globalAlpha = 1;
      ctx.restore();
    };
  };
}

// Draw multiple circles (batched for performance)
export function drawCircles_(context) {
  return function(specs) {
    return function() {
      const ctx = context.ctx;

      ctx.save();
      applyContextTransform(context);

      // Group by fill color and opacity for batching
      for (let i = 0; i < specs.length; i++) {
        const spec = specs[i];

        ctx.beginPath();
        ctx.arc(spec.x, spec.y, spec.radius, 0, Math.PI * 2);
        ctx.globalAlpha = spec.opacity;
        ctx.fillStyle = spec.fill;
        ctx.fill();

        if (spec.strokeWidth > 0) {
          ctx.strokeStyle = spec.stroke;
          ctx.lineWidth = spec.strokeWidth;
          ctx.stroke();
        }
      }

      ctx.globalAlpha = 1;
      ctx.restore();
    };
  };
}

// Draw multiple lines (batched for performance)
export function drawLines_(context) {
  return function(specs) {
    return function() {
      const ctx = context.ctx;

      ctx.save();
      applyContextTransform(context);

      // Batch all lines with same style
      // For now, draw each line (could optimize by grouping by stroke/opacity)
      for (let i = 0; i < specs.length; i++) {
        const spec = specs[i];

        ctx.beginPath();
        ctx.moveTo(spec.x1, spec.y1);
        ctx.lineTo(spec.x2, spec.y2);
        ctx.globalAlpha = spec.opacity;
        ctx.strokeStyle = spec.stroke;
        ctx.lineWidth = spec.strokeWidth;
        ctx.stroke();
      }

      ctx.globalAlpha = 1;
      ctx.restore();
    };
  };
}

// Begin a scene (clear and prepare)
export function beginScene_(context) {
  return function() {
    clearCanvas_(context)();
  };
}

// End a scene (currently no-op, but could flush batches)
export function endScene_(context) {
  return function() {
    // No-op for now - could be used for double-buffering
  };
}
