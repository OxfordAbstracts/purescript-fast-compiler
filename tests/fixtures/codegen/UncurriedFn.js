// Minimal FFI for mkFn2/runFn2 (from Data.Function.Uncurried)
export const mkFn2 = function (fn) {
  return function (a, b) {
    return fn(a)(b);
  };
};

export const runFn2 = function (fn) {
  return function (a) {
    return function (b) {
      return fn(a, b);
    };
  };
};
