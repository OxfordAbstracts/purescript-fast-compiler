import tls from "node:tls";

export const createServer = () => tls.createServer();
export const createServerOptionsImpl = (o) => tls.createServer(o);
export const addContextImpl = (s, hostname, context) => s.addContext(hostname, context);
export const getTicketKeysImpl = (s) => s.getTicketKeys();
export const setSecureContextImpl = (s, o) => s.setSecureContext(o);
export const setTicketKeysImpl = (s, b) => s.setTicketKeys(b);
