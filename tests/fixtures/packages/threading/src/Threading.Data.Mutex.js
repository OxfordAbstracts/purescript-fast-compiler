/**
 * @template T
 * @typedef {(g: Guard<T>) => () => void}
 * Waker
 */

/** @template T */
class Guard {
  released = false;

  /**
   * @param {Mutex<T>} mutex
   * @param {() => void} onExplicitRelease
   */
  constructor(mutex, onExplicitRelease) {
    this.mutex = mutex;
    this.cb = onExplicitRelease;
  }

  read() {
    if (this.released) {
      throw new Error("Guard#read after explicit release");
    }
    return this.mutex.a;
  }

  /** @param {T} a */
  write(a) {
    if (this.released) {
      throw new Error("Guard#write after explicit release");
    }
    this.mutex.a = a;
  }

  release() {
    if (!this.released) {
      this.released = true;
      this.cb();
    }
  }
}

/** @template T */
class Mutex {
  /** @type {WeakRef<Guard<T>> | undefined} */
  guard = undefined;

  /** @type {Array<(g: Guard<T>) => () => void>} */
  wakers = [];

  /** @type {FinalizationRegistry<undefined>} */
  cleanup = new FinalizationRegistry(() => this._guardReleased());

  /**
   * @param {T} a
   */
  constructor(a) {
    this.a = a;
  }

  _guardReleased() {
    this.guard = undefined;
    const wake = this.wakers.shift();
    if (wake) {
      wake(this._newGuard())();
    }
  }

  _newGuard() {
    const g = new Guard(this, () => {
      if (!this.guard) throw new Error("unreachable");
      this.cleanup.unregister(this.guard);
      this._guardReleased();
    });

    this.guard = new WeakRef(g);
    this.cleanup.register(g, undefined);
    return g;
  }

  locked() {
    return !!this.guard;
  }

  /** @param {Waker<T>} cb */
  lock(cb) {
    if (!this.guard) {
      cb(this._newGuard())();
      return undefined;
    } else {
      this.wakers.push(cb);
      return cb;
    }
  }

  /** @param {Waker<T>} cb */
  releaseWaker(cb) {
    const ix = this.wakers.indexOf(cb);
    if (ix > -1) {
      this.wakers.splice(ix, 1);
    }
  }

  tryLock() {
    if (!this.guard) {
      return this._newGuard();
    }
  }
}

/** @type {<T>(t: T) => () => Mutex<T>} */
export const _make = (a) => () => new Mutex(a);

/** @type {<T>(mutex: Mutex<T>) => (cb: Waker<T>) => () => Waker<T> | undefined} */
export const _lock = (mutex) => (cb) => () => mutex.lock(cb);

/** @type {<T>(mutex: Mutex<T>) => () => boolean} */
export const _locked = (mutex) => () => mutex.locked();

/** @type {<T>(mutex: Mutex<T>) => () => Guard<T> | undefined} */
export const _tryLock = (mutex) => () => mutex.tryLock();

/** @type {<T>(mutex: Mutex<T>) => (cb: Waker<T>) => () => void} */
export const _releaseWaker = (mutex) => (cb) => () => mutex.releaseWaker(cb);

/** @type {<T>(guard: Guard<T>) => () => void} */
export const _guardRelease = (g) => () => g.release();

/** @type {<T>(guard: Guard<T>) => () => T} */
export const _guardRead = (g) => () => g.read();

/** @type {<T>(guard: Guard<T>) => (t: T) => () => void} */
export const _guardWrite = (g) => (a) => () => g.write(a);
