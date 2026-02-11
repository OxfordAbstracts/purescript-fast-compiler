export const multiplyDOMMatrix = m1 => m2 => m1.multiply(m2);

export const invertDOMMatrix = m => m.inverse();

export const fromRecord = ({ a, b, c, d, e, f }) =>
  new DOMMatrixReadOnly([a, b, c, d, e, f]);

export const toRecord = m => ({ a: m.a, b: m.b, c: m.c, d: m.d, e: m.e, f: m.f });

export const getTransformImpl = ctx => () => ctx.getTransform();
