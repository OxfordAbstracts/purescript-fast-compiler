'use strict';

import { randomBytes } from "crypto";

export function prng() {
  return randomBytes(1).readUInt8() / 0xff;
}
