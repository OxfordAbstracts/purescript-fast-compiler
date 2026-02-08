/** @type {(_: Record<string, Array<string | File>>) => () => FormData} */
export const unsafeMakeFormData = o => () => {
  const form = new FormData()

  Object.entries(o).forEach(([k, vs]) => {
    vs.forEach(v => {
      form.append(k, v)
    })
  })

  return form
}

/** @typedef {{filename: string, mime: string, buf: ArrayBuffer}} FileRecord */

/** @type {(_: FileRecord) => () => File} */
export const unsafeMakeFile =
  ({ mime, buf, filename }) =>
  () =>
    new File([buf], filename, { type: mime })

/** @type {(_: FormData) => () => Promise<Record<string, Array<string | FileRecord>>>} */
export const unsafeUnmakeFormData = fd => async () => {
  /** @type {Record<string, Array<string | FileRecord>>} */
  const rec = {}
  for (const [k, ent_] of fd.entries()) {
    /** @type {File | string} */
    const ent = ent_

    /** @type {string | FileRecord} */
    let append = ''
    if (ent instanceof File) {
      append = {
        filename: ent.name,
        buf: await ent.arrayBuffer(),
        mime: ent.type,
      }
    } else {
      append = ent
    }

    if (!append) {
      continue
    }

    if (rec[k]) {
      rec[k].push(append)
    } else {
      rec[k] = [append]
    }
  }

  return rec
}

/** @type {(a: ArrayBuffer) => (b: ArrayBuffer) => boolean} */
export const unsafeEqArrayBuffer = a => b => {
  try {
    if (a.byteLength !== b.byteLength) return false
    const ua = new Uint8Array(a)
    const ub = new Uint8Array(b)
    let pass = true
    for (let i = 0; i < a.byteLength; i++) {
      pass = pass && ua[i] === ub[i]
    }

    return pass
  } catch {
    return false
  }
}

/** @type {(a: ArrayBuffer) => string} */
export const unsafeShowArrayBuffer = a => {
  try {
    return Buffer.from(a).toString('base64url')
  } catch (e) {
    return e instanceof Error ? e.toString() : ''
  }
}
