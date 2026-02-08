export const _registerCsiHandler = parser => fi => cb => () => parser.registerCsiHandler(fi,p => cb(p)());
export const _registerDcsHandler = parser => fi => cb => () => parser.registerDcsHandler(fi,(s,p) => cb(s)(p)());
export const _registerEscHandler = parser => fi => cb => () => parser.registerEscHandler(fi,cb);
export const _registerOscHandler = parser => fi => cb => () => parser.registerOscHandler(fi,s => cb(s)());
