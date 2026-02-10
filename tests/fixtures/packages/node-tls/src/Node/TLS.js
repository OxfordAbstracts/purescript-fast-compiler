import tls from "node:tls";
export { 
  rootCertificates, 
  DEFAULT_ECDH_CURVE as defaultEcdhCurve,
  DEFAULT_MAX_VERSION as defaultMinVersion,
  DEFAULT_MIN_VERSION as defaultMaxVersion,
  DEFAULT_CIPHERS as defaultCiphers,
} from "node:tls";

export const checkServerIdentityImpl = (hostname, cert) => tls.checkServerIdentity(hostname, cert);
export const createSecureContext = () => tls.createSecureContext();
export const createSecureContextOptionsImpl = (o) => tls.createSecureContext(o);
export const getCiphers = () => tls.getCiphers();

