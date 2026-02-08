export function encodeImpl (str) {
  const encoder = new TextEncoder();

  return encoder.encode(str);
};
