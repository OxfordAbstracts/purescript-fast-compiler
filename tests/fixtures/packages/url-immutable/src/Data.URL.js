/** @type {(u: URL) => URL} */
const clone = u => new URL(u.href)

/** @type {(s: string) => URL | null} */
export const fromStringImpl = s => {
  try {
    return new URL(s)
  } catch {
    return null
  }
}

/** @type {(u: URL) => string | null} */
export const hashImpl = u => u.hash

/** @type {(u: URL) => string | null} */
export const hostImpl = u => u.hostname

/** @type {(u: URL) => string | null} */
export const hrefImpl = u => u.href

/** @type {(u: URL) => string | null} */
export const originImpl = u => u.origin

/** @type {(u: URL) => string | null} */
export const passwordImpl = u => u.password

/** @type {(u: URL) => string | null} */
export const pathnameImpl = u => u.pathname

/** @type {(u: URL) => string | null} */
export const portImpl = u => u.port

/** @type {(u: URL) => string | null} */
export const protocolImpl = u => u.protocol

/** @type {(u: URL) => string | null} */
export const searchImpl = u => u.search

/** @type {(u: URL) => URLSearchParams} */
export const searchParamsImpl = u => u.searchParams

/** @type {(u: URL) => string | null} */
export const usernameImpl = u => u.username

/** @type {(u: URL) => Array<string>} */
export const queryKeysImpl = u => Array.from(u.searchParams.keys())

/** @type {(k: string) => (u: URL) => Array<string>} */
export const queryLookupImpl = k => u => u.searchParams.getAll(k)

/** @type {(qs: Array<{k: string, vs: Array<string>}>) => (u: URL) => URL} */
export const querySetAllImpl = qs => u => {
  const u_ = clone(u)
  u_.search = ''
  qs.forEach(({ k, vs }) => {
    vs.forEach(v => u_.searchParams.append(k, v))
  })
  return u_
}

/** @type {(k: string) => (vs: Array<string>) => (u: URL) => URL} */
export const queryPutImpl = k => vs => u => {
  const u_ = clone(u)
  u_.searchParams.delete(k)
  vs.forEach(v => u_.searchParams.append(k, v))
  return u_
}

/** @type {(k: string) => (v: string | null) => (u: URL) => URL} */
export const queryAppendImpl = k => v => u => {
  const u_ = clone(u)
  u_.searchParams.append(k, v || '')
  return u_
}

/** @type {(k: string) => (u: URL) => URL} */
export const queryDeleteImpl = k => u => {
  const u_ = clone(u)
  u_.searchParams.delete(k)
  return u_
}

/** @type {(_s: string) => (u: URL) => URL} */
export const setHashImpl = s => u => {
  const u_ = clone(u)
  u_.hash = s
  return u_
}

/** @type {(_s: string) => (u: URL) => URL} */
export const setHostImpl = s => u => {
  const u_ = clone(u)
  u_.hostname = s
  return u_
}

/** @type {(_s: string) => (u: URL) => URL} */
export const setHrefImpl = s => u => {
  const u_ = clone(u)
  u_.href = s
  return u_
}

/** @type {(_s: string) => (u: URL) => URL} */
export const setPasswordImpl = s => u => {
  const u_ = clone(u)
  u_.password = s
  return u_
}

/** @type {(_s: string) => (u: URL) => URL} */
export const setPathnameImpl = s => u => {
  const u_ = clone(u)
  u_.pathname = s
  return u_
}

/** @type {(_s: string) => (u: URL) => URL} */
export const setPortImpl = s => u => {
  const u_ = clone(u)
  u_.port = s
  return u_
}

/** @type {(_s: string) => (u: URL) => URL} */
export const setProtocolImpl = s => u => {
  const u_ = clone(u)
  u_.protocol = s
  return u_
}

/** @type {(_s: string) => (u: URL) => URL} */
export const setSearchImpl = s => u => {
  const u_ = clone(u)
  u_.search = s
  return u_
}

/** @type {(_s: string) => (u: URL) => URL} */
export const setUsernameImpl = s => u => {
  const u_ = clone(u)
  u_.username = s
  return u_
}
