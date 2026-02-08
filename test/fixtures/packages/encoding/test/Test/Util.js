// Inspired by `purescript-typedarray`. Unfortunately, the future of that
// library is currently (2024-01-26) uncertain.
export function asUint8ArrayImpl (array) {
  return new Uint8Array(array);
}
