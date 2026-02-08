export const iLogger = l => {
  return {
    trace: (msg, ...args) => l.trace(msg)(args)()
  , debug: (msg, ...args) => l.debug(msg)(args)()
  , info: (msg, ...args) => l.info(msg)(args)()
  , warn: (msg, ...args) => l.warn(msg)(args)()
  , error: (msg, ...args) => l.error(typeof msg === 'string' ? new Error(msg) : msg)(args)()
  }
}
