import {decode, encode} from 'cbor-x'

/** @type {(a: Buffer) => () => unknown} */
export const decodeImpl = buf => () => decode(buf)

/** @type {(a: unknown) => () => Buffer} */
export const encodeImpl = buf => () => encode(buf)
