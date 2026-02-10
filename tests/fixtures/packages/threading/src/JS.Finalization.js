/** @type {<T>(cb: (t: T) => void) => () => FinalizationRegistry<T>} */
export const registry = (cb) => () => new FinalizationRegistry(cb);

/** @type {<T>(f: FinalizationRegistry<T>) => <O extends WeakKey>(a: WeakRef<O>) => (b: T) => () => void} */
export const register = (fin) => (a) => (b) => () => fin.register(a, b);

/** @type {<T>(f: FinalizationRegistry<T>) => <O extends WeakKey>(a: WeakRef<O>) => () => void} */
export const unregister = (fin) => (a) => () => fin.unregister(a);
