import { EncoderStream } from "cbor-x";

/** @type {(s: import('cbor-x').Options) => () => EncoderStream} */
export const makeImpl = (c) => () => new EncoderStream({useRecords: false, ...c, allowHalfOpen: true});

/** @type {(s: EncoderStream) => (a: unknown) => () => void} */
export const writeImpl = (s) => (a) => () => s.write(a);
