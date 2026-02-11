export const addPathImpl = path2 => matrix => path1 => () =>
  void path1.addPath(path2, matrix);

export const closePathImpl = path => () => void path.closePath();

export const moveToImpl = x => y => path => () => void path.moveTo(x, y);

export const lineToImpl = x => y => path => () => void path.lineTo(x, y);

export const bezierCurveToImpl = cp1x => cp1y => cp2x => cp2y => x => y =>
  path => () => void path.bezierCurveTo(cp1x, cp1y, cp2x, cp2y, x, y);

export const quadraticCurveToImpl = cpx => cpy => x => y =>
  path => () => void path.quadraticCurveTo(cpx, cpy, x, y);

export const arcToImpl = x1 => y1 => x2 => y2 => radius => path => () =>
  void path.arcTo(x1, y1, x2, y2, radius);

export const ellipseImpl = x => y => radiusX => radiusY => rotation => startAngle =>
  endAngle => anticlockwise => path => () => void path.ellipse(
    x, y,
    radiusX, radiusY,
    rotation,
    startAngle, endAngle,
    anticlockwise
  );

export const rectImpl = x => y => width => height => path => () =>
  void path.rect(x, y, width, height)


export const newPath2DImpl = () => new Path2D();

export const fillImpl = ctx => path => fillRule => () =>
  void ctx.fill(path, fillRule);

export const strokeImpl = ctx => path => () => void ctx.stroke(path);

export const clipImpl = ctx => path => fillRule => () =>
  void ctx.clip(path, fillRule);
