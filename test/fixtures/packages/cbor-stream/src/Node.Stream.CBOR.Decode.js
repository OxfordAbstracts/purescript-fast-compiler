import { DecoderStream } from "cbor-x";

/** @type {(s: import('cbor-x').Options) => () => DecoderStream} */
export const makeImpl = (c) => () => new DecoderStream({useRecords: false, ...c, allowHalfOpen: true});

/** @type {(s: DecoderStream) => () => unknown | null} */
export const readImpl = (p) => () => p.read();
