'use strict';

export function prng() {
  const webCrypto = window.crypto || window.msCrypto;
  const buf = new Uint8Array(1);
  webCrypto.getRandomValues(buf);
  return buf[0] / 0xff;
}
