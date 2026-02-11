export const styleIsString = style => typeof style == "string";

export const styleIsGradient = style => style instanceof CanvasGradient;

export const styleIsPattern = style => style instanceof CanvasGradient;

export const getCanvasEffect = ctx => () => ctx.canvas;

export const setFillStyleImpl = ctx => style => () => void (ctx.fillStyle = style);

export const setStrokeStyleImpl = ctx => style => () =>
  void (ctx.strokeStyle = style);

export const getFillStyleImpl = ctx => () => ctx.fillStyle;

export const getStrokeStyleImpl = ctx => () => ctx.strokeStyle;

export const setImageSmoothingImpl = ctx => bool => () => void
  (ctx.imageSmoothingEnabled = bool);

export const getImageSmoothingImpl = ctx => () => ctx.imageSmoothingEnabled;
