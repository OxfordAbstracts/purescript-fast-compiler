/** @type {(_: Blob) => () => Promise<ArrayBuffer>} */
export const blobArrayBufferImpl = b => () => b.arrayBuffer()

/** @type {(_: FormDataEntryValue) => number} */
const formDataValueSize = v => (typeof v === 'string' ? v.length : v.size)

/** @type {(_: ArrayBuffer | FormData) => () => number} */
export const rawBodySize = body => () =>
  body instanceof ArrayBuffer
    ? body.byteLength
    : body instanceof FormData
      ? Array.from(body.entries()).reduce(
          (size, [k, v]) => size + k.length + formDataValueSize(v),
          0,
        )
      : 0
