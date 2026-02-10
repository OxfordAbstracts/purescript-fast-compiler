module Node.TLS.Types where

import Prelude

import Data.Nullable (Nullable)
import Effect.Exception (Error)
import Effect.Uncurried (EffectFn2)
import Foreign (Foreign)
import Node.Buffer (Buffer)
import Node.Net.Types (Socket, TCP)
import Node.Net.Types as NetTypes

-- | Type-level tag that indicates whether the value is a server or client one.
data Endpoint

foreign import data Client :: Endpoint
foreign import data Server :: Endpoint

-- | `TlsSocket` extends `Node.Net.Types (Socket)`, `Node.Stream.Types (Duplex)`, and `Node.EventEmitter (EventEmitter)`
foreign import data TlsSocket :: Endpoint -> Type

-- | `TlsServer` extends `Node.Net.Types (Server)` and `Node.EventEmitter (EventEmitter)`
foreign import data TlsServer :: Type

foreign import data SecureContext :: Type

-- | `name` <string> OpenSSL name for the cipher suite.
-- | `standardName` <string> IETF name for the cipher suite.
-- | `version` <string> The minimum TLS protocol version supported by this cipher suite. For the actual negotiated protocol, see tls.TLSSocket.getProtocol().
type CipherObject =
  { name :: String
  , standardName :: String
  , version :: String
  }

type EphemeralKeyInfoDH =
  { type :: String
  , size :: Int
  }

type EphemeralKeyInfoECDH =
  { type :: String
  , name :: String
  , size :: Int
  }

-- | `enableTrace`: If true, `tls.TLSSocket.enableTrace()` will be called on new connections. Tracing can be enabled after the secure connection is established, but this option must be used to trace the secure connection setup. Default: false.
-- | `isServer`: The SSL/TLS protocol is asymmetrical, TLSSockets must know if they are to behave as a server or a client. If true the TLS socket will be instantiated as a server. Default: false.
-- | `server` <net.Server> A net.Server instance.
-- | `requestCert`: Whether to authenticate the remote peer by requesting a certificate. Clients always request a server certificate. Servers (isServer is true) may set requestCert to true to request a client certificate.
-- | `rejectUnauthorized`: If not false the server will reject any connection which is not authorized with the list of supplied CAs. This option only has an effect if requestCert is true. Default: true.
-- | `ALPNProtocols`: <string[]> | <Buffer[]> | <TypedArray[]> | <DataView[]> | <Buffer> | <TypedArray> | <DataView> An array of strings, Buffers, TypedArrays, or DataViews, or a single Buffer, TypedArray, or DataView containing the supported ALPN protocols. Buffers should have the format [len][name][len][name]... e.g. 0x05hello0x05world, where the first byte is the length of the next protocol name. Passing an array is usually much simpler, e.g. ['hello', 'world']. (Protocols should be ordered by their priority.)
-- | `SNICallback`: A function that will be called if the client supports SNI TLS extension. Two arguments will be passed when called: servername and callback. callback is an error-first callback that takes two optional arguments: error and ctx. ctx, if provided, is a SecureContext instance. tls.createSecureContext() can be used to get a proper SecureContext. If callback is called with a falsy ctx argument, the default secure context of the server will be used. If SNICallback wasn't provided the default callback with high-level API will be used (see below).
-- | `session` <Buffer> A Buffer instance containing a TLS session.
-- | `requestOCSP` <boolean> If true, specifies that the OCSP status request extension will be added to the client hello and an 'OCSPResponse' event will be emitted on the socket before establishing a secure communication
type NewTlsSocketOptions r =
  ( enableTrace :: Boolean
  , isServer :: Boolean
  , server :: NetTypes.Server TCP
  , requestCert :: Boolean
  , rejectUnauthorized :: Boolean
  , "ALPNProtocols" :: Array Buffer
  , "SNICallback" :: EffectFn2 String (EffectFn2 (Nullable Error) (Nullable SecureContext) Unit) Unit
  , session :: Buffer
  , requestOCSP :: Boolean
  | r
  )

-- | `enableTrace`: See tls.createServer()
-- | `host` <string> Host the client should connect to. Default: 'localhost'.
-- | `port` <number> Port the client should connect to.
-- | `socket` <stream.Duplex> Establish secure connection on a given socket rather than creating a new socket. Typically, this is an instance of net.Socket, but any Duplex stream is allowed. If this option is specified, path, host, and port are ignored, except for certificate validation. Usually, a socket is already connected when passed to tls.connect(), but it can be connected later. Connection/disconnection/destruction of socket is the user's responsibility; calling tls.connect() will not cause net.connect() to be called.
-- | `allowHalfOpen` <boolean> If set to false, then the socket will automatically end the writable side when the readable side ends. If the socket option is set, this option has no effect. See the allowHalfOpen option of net.Socket for details. Default: false.
-- | `rejectUnauthorized` <boolean> If not false, the server certificate is verified against the list of supplied CAs. An 'error' event is emitted if verification fails; err.code contains the OpenSSL error code. Default: true.
-- | `pskCallback` <Function>
-- |    - hint: <string> optional message sent from the server to help client decide which identity to use during negotiation. Always null if TLS 1.3 is used.
-- |    - Returns`: <Object> in the form { psk: <Buffer|TypedArray|DataView>, identity: <string> } or null to stop the negotiation process. psk must be compatible with the selected cipher's digest. identity must use UTF-8 encoding.
-- |    When negotiating TLS-PSK (pre-shared keys), this function is called with optional identity hint provided by the server or null in case of TLS 1.3 where hint was removed. It will be necessary to provide a custom tls.checkServerIdentity() for the connection as the default one will try to check host name/IP of the server against the certificate but that's not applicable for PSK because there won't be a certificate present. More information can be found in the RFC 4279.
-- | `ALPNProtocols`: <string[]> | <Buffer[]> | <TypedArray[]> | <DataView[]> | <Buffer> | <TypedArray> | <DataView> An array of strings, Buffers, TypedArrays, or DataViews, or a single Buffer, TypedArray, or DataView containing the supported ALPN protocols. Buffers should have the format [len][name][len][name]... e.g. '\x08http/1.1\x08http/1.0', where the len byte is the length of the next protocol name. Passing an array is usually much simpler, e.g. ['http/1.1', 'http/1.0']. Protocols earlier in the list have higher preference than those later.
-- | `servername`: <string> Server name for the SNI (Server Name Indication) TLS extension. It is the name of the host being connected to, and must be a host name, and not an IP address. It can be used by a multi-homed server to choose the correct certificate to present to the client, see the SNICallback option to tls.createServer().
-- | `checkServerIdentity`(servername, cert) <Function> A callback function to be used (instead of the builtin tls.checkServerIdentity() function) when checking the server's host name (or the provided servername when explicitly set) against the certificate. This should return an <Error> if verification fails. The method should return undefined if the servername and cert are verified.
-- | `session` <Buffer> A Buffer instance, containing TLS session.
-- | `minDHSize` <number> Minimum size of the DH parameter in bits to accept a TLS connection. When a server offers a DH parameter with a size less than minDHSize, the TLS connection is destroyed and an error is thrown. Default: 1024.
-- | `highWaterMark`: <number> Consistent with the readable stream highWaterMark parameter. Default: 16 * 1024.
-- | `secureContext`: TLS context object created with tls.createSecureContext(). If a secureContext is not provided, one will be created by passing the entire options object to tls.createSecureContext().
type ConnectTlsSocketOptions endpoint r =
  ( enableTrace :: Boolean
  , host :: String
  , port :: Int
  , socket :: Socket TCP
  , allowHalfOpen :: Boolean
  , rejectUnauthorized :: Boolean
  , pskCallback :: EffectFn2 (TlsSocket endpoint) String Buffer
  , "ALPNProtocols" :: Array Buffer
  , servername :: String
  , checkServerIdentity :: EffectFn2 String Foreign (Nullable Error)
  , session :: Buffer
  , minDHSize :: Int
  , highWaterMark :: Int
  | r
  )

-- | `ca` <string> | <string[]> | <Buffer> | <Buffer[]> Optionally override the trusted CA certificates. Default is to trust the well-known CAs curated by Mozilla. Mozilla's CAs are completely replaced when CAs are explicitly specified using this option. The value can be a string or Buffer, or an Array of strings and/or Buffers. Any string or Buffer can contain multiple PEM CAs concatenated together. The peer's certificate must be chainable to a CA trusted by the server for the connection to be authenticated. When using certificates that are not chainable to a well-known CA, the certificate's CA must be explicitly specified as a trusted or the connection will fail to authenticate. If the peer uses a certificate that doesn't match or chain to one of the default CAs, use the ca option to provide a CA certificate that the peer's certificate can match or chain to. For self-signed certificates, the certificate is its own CA, and must be provided. For PEM encoded certificates, supported types are "TRUSTED CERTIFICATE", "X509 CERTIFICATE", and "CERTIFICATE". See also tls.rootCertificates.
-- | `cert` <string> | <string[]> | <Buffer> | <Buffer[]> Cert chains in PEM format. One cert chain should be provided per private key. Each cert chain should consist of the PEM formatted certificate for a provided private key, followed by the PEM formatted intermediate certificates (if any), in order, and not including the root CA (the root CA must be pre-known to the peer, see ca). When providing multiple cert chains, they do not have to be in the same order as their private keys in key. If the intermediate certificates are not provided, the peer will not be able to validate the certificate, and the handshake will fail.
-- | `sigalgs` <string> Colon-separated list of supported signature algorithms. The list can contain digest algorithms (SHA256, MD5 etc.), public key algorithms (RSA-PSS, ECDSA etc.), combination of both (e.g 'RSA+SHA384') or TLS v1.3 scheme names (e.g. rsa_pss_pss_sha512). See OpenSSL man pages for more info.
-- | `ciphers` <string> Cipher suite specification, replacing the default. For more information, see Modifying the default TLS cipher suite. Permitted ciphers can be obtained via tls.getCiphers(). Cipher names must be uppercased in order for OpenSSL to accept them.
-- | `clientCertEngine` <string> Name of an OpenSSL engine which can provide the client certificate.
-- | `crl` <string> | <string[]> | <Buffer> | <Buffer[]> PEM formatted CRLs (Certificate Revocation Lists).
-- | `dhparam` <string> | <Buffer> 'auto' or custom Diffie-Hellman parameters, required for non-ECDHE perfect forward secrecy. If omitted or invalid, the parameters are silently discarded and DHE ciphers will not be available. ECDHE-based perfect forward secrecy will still be available.
-- | `ecdhCurve` <string> A string describing a named curve or a colon separated list of curve NIDs or names, for example P-521:P-384:P-256, to use for ECDH key agreement. Set to auto to select the curve automatically. Use crypto.getCurves() to obtain a list of available curve names. On recent releases, openssl ecparam -list_curves will also display the name and description of each available elliptic curve. Default: tls.DEFAULT_ECDH_CURVE.
-- | `honorCipherOrder` <boolean> Attempt to use the server's cipher suite preferences instead of the client's. When true, causes SSL_OP_CIPHER_SERVER_PREFERENCE to be set in secureOptions, see OpenSSL Options for more information.
-- | `key` <string> | <string[]> | <Buffer> | <Buffer[]> | <Object[]> Private keys in PEM format. PEM allows the option of private keys being encrypted. Encrypted keys will be decrypted with options.passphrase. Multiple keys using different algorithms can be provided either as an array of unencrypted key strings or buffers, or an array of objects in the form {pem: <string|buffer>[, passphrase: <string>]}. The object form can only occur in an array. object.passphrase is optional. Encrypted keys will be decrypted with object.passphrase if provided, or options.passphrase if it is not.
-- | `privateKeyEngine` <string> Name of an OpenSSL engine to get private key from. Should be used together with privateKeyIdentifier.
-- | `privateKeyIdentifier` <string> Identifier of a private key managed by an OpenSSL engine. Should be used together with privateKeyEngine. Should not be set together with key, because both options define a private key in different ways.
-- | `maxVersion` <string> Optionally set the maximum TLS version to allow. One of 'TLSv1.3', 'TLSv1.2', 'TLSv1.1', or 'TLSv1'. Cannot be specified along with the secureProtocol option; use one or the other. Default: tls.DEFAULT_MAX_VERSION.
-- | `minVersion` <string> Optionally set the minimum TLS version to allow. One of 'TLSv1.3', 'TLSv1.2', 'TLSv1.1', or 'TLSv1'. Cannot be specified along with the secureProtocol option; use one or the other. Avoid setting to less than TLSv1.2, but it may be required for interoperability. Default: tls.DEFAULT_MIN_VERSION.
-- | `passphrase` <string> Shared passphrase used for a single private key and/or a PFX.
-- | `pfx` <string> | <string[]> | <Buffer> | <Buffer[]> | <Object[]> PFX or PKCS12 encoded private key and certificate chain. pfx is an alternative to providing key and cert individually. PFX is usually encrypted, if it is, passphrase will be used to decrypt it. Multiple PFX can be provided either as an array of unencrypted PFX buffers, or an array of objects in the form {buf: <string|buffer>[, passphrase: <string>]}. The object form can only occur in an array. object.passphrase is optional. Encrypted PFX will be decrypted with object.passphrase if provided, or options.passphrase if it is not.
-- | `secureOptions` <number> Optionally affect the OpenSSL protocol behavior, which is not usually necessary. This should be used carefully if at all! Value is a numeric bitmask of the SSL_OP_* options from OpenSSL Options.
-- | `sessionIdContext` <string> Opaque identifier used by servers to ensure session state is not shared between applications. Unused by clients.
-- | `ticketKeys`: <Buffer> 48-bytes of cryptographically strong pseudorandom data. See Session Resumption for more information.
-- | `sessionTimeout` <number> The number of seconds after which a TLS session created by the server will no longer be resumable. See Session Resumption for more information. Default: 300.
-- |
-- | Note: `secureProtocol` is not supported because it cannot be used if `minVersion`/`maxVersion` are used
type CreateSecureContextOptions :: Row Type -> Row Type
type CreateSecureContextOptions r =
  ( ca :: Array Buffer
  , cert :: Array Buffer
  , sigalgs :: String
  , ciphers :: String
  , clientCertEngine :: String
  , crl :: Array Buffer
  , dhparam :: Array Buffer
  , ecdhCurve :: String
  , honorCipherOrder :: Boolean
  , key :: Array Buffer
  , privateKeyEngine :: String
  , privateKeyIdentifier :: String
  , maxVersion :: String
  , minVersion :: String
  , passphrase :: String
  , pfx :: Array Buffer
  , secureOptions :: Int
  , sessionIdContext :: String
  , ticketKeys :: Buffer
  , sessionTimeout :: Int
  | r
  )

-- | `handshakeTimeout` <number> Abort the connection if the SSL/TLS handshake does not finish in the specified number of milliseconds. A 'tlsClientError' is emitted on the tls.Server object whenever a handshake times out. Default: 120000 (120 seconds).
-- | `pskCallback` <Function>
-- |    - socket: <tls.TLSSocket> the server tls.TLSSocket instance for this connection.
-- |    - identity: <string> identity parameter sent from the client.
-- |    - Returns: <Buffer> | <TypedArray> | <DataView> pre-shared key that must either be a buffer or null to stop the negotiation process. Returned PSK must be compatible with the selected cipher's digest.
-- |    When negotiating TLS-PSK (pre-shared keys), this function is called with the identity provided by the client. If the return value is null the negotiation process will stop and an "unknown_psk_identity" alert message will be sent to the other party. If the server wishes to hide the fact that the PSK identity was not known, the callback must provide some random data as psk to make the connection fail with "decrypt_error" before negotiation is finished. PSK ciphers are disabled by default, and using TLS-PSK thus requires explicitly specifying a cipher suite with the ciphers option. More information can be found in the RFC 4279.
-- | `pskIdentityHint` <string> optional hint to send to a client to help with selecting the identity during TLS-PSK negotiation. Will be ignored in TLS 1.3. Upon failing to set pskIdentityHint 'tlsClientError' will be emitted with 'ERR_TLS_PSK_SET_IDENTIY_HINT_FAILED' code.
type TlsCreateServerOptions :: Endpoint -> Row Type -> Row Type
type TlsCreateServerOptions endpoint r =
  ( handshakeTimeout :: Int
  , pskCallback :: EffectFn2 (TlsSocket endpoint) String Buffer
  , pskIdentityHint :: String
  | r
  )
