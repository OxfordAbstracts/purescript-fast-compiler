import { Readable } from 'stream'
import { Buffer } from 'buffer'

/** @type {(r: Response) => () => Promise<Buffer>} */
export const bufferImpl = r => async () => Buffer.from(await r.arrayBuffer())

/** @type {(r: Response) => () => Readable} */
export const streamImpl = r => () => {
  if (!r.body) {
    throw new Error('Response body is empty')
  }

  const reader = r.body.getReader()
  return new Readable({
    read() {
      reader
        .read()
        .then(chunk => {
          if (chunk.value) {
            this.push(Buffer.from(chunk.value))
          }

          if (chunk.done) {
            this.push(null)
          }
        })
        .catch(e => this.destroy(e))
    },
  })
}
