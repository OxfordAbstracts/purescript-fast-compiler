/** @type {<T extends WeakKey>(_: T) => () => WeakRef<T>} */
export const make = (a) => () => new WeakRef(a);

/** @type {<T extends WeakKey>(_: WeakRef<T>) => () => T | undefined} */
export const _deref = (a) => () => a.deref();
