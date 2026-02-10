import {FLOAT32_OPTIONS} from 'cbor-x'

/** @type {<F32>(o: {round: (_a: F32) => boolean, fit: (_a: F32) => boolean, always: (_a: F32) => boolean}) => (f: F32) => FLOAT32_OPTIONS} */
export const f32ToConst = ({round, fit, always}) => a => 
  round(a)
  ? FLOAT32_OPTIONS.ALWAYS
  : fit(a)
  ? FLOAT32_OPTIONS.DECIMAL_FIT
  : round(a)
  ? FLOAT32_OPTIONS.DECIMAL_ROUND
  : FLOAT32_OPTIONS.NEVER
