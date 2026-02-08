/**
 * @typedef {{
 *   body: string | ArrayBuffer | Blob | FormData | null,
 *   headers: Record<string, string>,
 *   credentials: RequestCredentials,
 *   method: string,
 *   url: string,
 * }} RequestInit
 */

/** @type {(o: RequestInit) => () => Promise<Response>} */
export const fetchImpl = o => () => fetch(o.url, { ...o, redirect: 'manual' })
