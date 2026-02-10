/// <reference lib="dom" />

/** @type {(_: Response) => () => Response} */
export const cloneImpl = rep => () => rep.clone()

/** @type {(_: Response) => () => ReadableStream} */
export const streamImpl = rep => () => rep.body

/** @type {(_: Response) => () => Promise<unknown>} */
export const jsonImpl = rep => () => rep.json()

/** @type {(_: Response) => () => Promise<string>} */
export const textImpl = rep => () => rep.text()

/** @type {(_: Response) => () => Promise<ArrayBuffer>} */
export const abImpl = rep => () => rep.arrayBuffer()

/** @type {(_: Response) => () => Promise<Blob>} */
export const blobImpl = rep => () => rep.blob()

/** @type {(_: Response) => () => Promise<FormData>} */
export const formImpl = rep => () => rep.formData()

/** @type {(_: Response) => () => number} */
export const statusImpl = rep => () => rep.status

/** @type {(_: Response) => () => string} */
export const statusTextImpl = rep => () => rep.statusText

/** @type {(_: Response) => () => Record<string, string>} */
export const headersImpl = rep => () => {
  /** @type {Record<string, string>} */
  const hs = {}

  Array.from(rep.headers.entries()).forEach(([k, v]) => {
    hs[k] = v
  })

  return hs
}
