// FFI for Conversions module

export const parseNumberOrZero = (s) => {
  const n = parseFloat(s);
  return isNaN(n) ? 0.0 : n;
};

export const isNumericString = (s) => {
  return !isNaN(parseFloat(s)) && isFinite(s);
};
