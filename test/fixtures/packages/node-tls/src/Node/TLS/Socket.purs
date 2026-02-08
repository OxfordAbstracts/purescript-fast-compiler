module Node.TLS.Socket
  ( toTcpSocket
  , newClientTlsSocket
  , newClientTlsSocket'
  , newServerTlsSocket
  , newServerTlsSocket'
  , connectClient
  , connectServer
  , keylogHandle
  , ocspResponseHandle
  , secureContextHandle
  , sessionHandle
  , authorizationError
  , authorized
  , enableTrace
  , encrypted
  , exportKeyingMaterial
  , exportKeyingMaterial'
  , getCertificate
  , getCipher
  , getEphemeralKeyInfo
  , getFinished
  , getPeerCertificate
  , getPeerCertificate'
  , getPeerFinished
  , getPeerX509Certificate
  , getProtocol
  , getSession
  , getSharedSigalgs
  , getTLSTicket
  , getX509Certificate
  , isSessionReused
  , setMaxSendFragment
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Data.Nullable (Nullable, toMaybe)
import Effect (Effect)
import Effect.Uncurried (EffectFn1, EffectFn2, EffectFn3, EffectFn4, mkEffectFn1, runEffectFn1, runEffectFn2, runEffectFn3, runEffectFn4)
import Foreign (Foreign)
import Node.Buffer (Buffer)
import Node.EventEmitter (EventHandle(..))
import Node.EventEmitter.UtilTypes (EventHandle1, EventHandle0)
import Node.Net.Types (ConnectTcpOptions, Socket, TCP)
import Node.TLS.Types (CipherObject, Client, ConnectTlsSocketOptions, CreateSecureContextOptions, EphemeralKeyInfoDH, EphemeralKeyInfoECDH, NewTlsSocketOptions, Server, TlsSocket)
import Partial.Unsafe (unsafeCrashWith)
import Prim.Row as Row
import Unsafe.Coerce (unsafeCoerce)

toTcpSocket :: forall endpoint. TlsSocket endpoint -> Socket TCP
toTcpSocket = unsafeCoerce

newClientTlsSocket :: Socket TCP -> Effect (TlsSocket Client)
newClientTlsSocket s = runEffectFn1 newTlsSocketImpl s

newServerTlsSocket :: Socket TCP -> Effect (TlsSocket Server)
newServerTlsSocket s = runEffectFn1 newTlsSocketImpl s

foreign import newTlsSocketImpl :: forall endpoint. EffectFn1 (Socket TCP) (TlsSocket endpoint)

newClientTlsSocket'
  :: forall r trash
   . Row.Union r trash (NewTlsSocketOptions (CreateSecureContextOptions ()))
  => Socket TCP
  -> { | r }
  -> Effect (TlsSocket Client)
newClientTlsSocket' s o = runEffectFn2 newTlsSocketOptionsImpl s o

newServerTlsSocket'
  :: forall r trash
   . Row.Union r trash (NewTlsSocketOptions (CreateSecureContextOptions ()))
  => Socket TCP
  -> { | r }
  -> Effect (TlsSocket Server)
newServerTlsSocket' s o = runEffectFn2 newTlsSocketOptionsImpl s o

foreign import newTlsSocketOptionsImpl :: forall r endpoint. EffectFn2 (Socket TCP) ({ | r }) (TlsSocket endpoint)

connectClient
  :: forall r trash
   . Row.Union r trash (ConnectTlsSocketOptions Client (CreateSecureContextOptions (ConnectTcpOptions ())))
  => { | r }
  -> Effect (TlsSocket Client)
connectClient o = runEffectFn1 connectImpl o

connectServer
  :: forall r trash
   . Row.Union r trash (ConnectTlsSocketOptions Server (CreateSecureContextOptions (ConnectTcpOptions ())))
  => { | r }
  -> Effect (TlsSocket Server)
connectServer o = runEffectFn1 connectImpl o

foreign import connectImpl :: forall endpoint r. EffectFn1 ({ | r }) (TlsSocket endpoint)

keylogHandle :: forall endpoint. EventHandle1 (TlsSocket endpoint) Buffer
keylogHandle = EventHandle "keylog" mkEffectFn1

ocspResponseHandle :: forall endpoint. EventHandle1 (TlsSocket endpoint) Buffer
ocspResponseHandle = EventHandle "OCSPResponse" mkEffectFn1

secureContextHandle :: forall endpoint. EventHandle0 (TlsSocket endpoint)
secureContextHandle = EventHandle "secureContext" identity

sessionHandle :: forall endpoint. EventHandle1 (TlsSocket endpoint) Buffer
sessionHandle = EventHandle "session" mkEffectFn1

authorizationError :: forall endpoint. TlsSocket endpoint -> Effect Foreign
authorizationError s = runEffectFn1 authorizationErrorImpl s

foreign import authorizationErrorImpl :: forall endpoint. EffectFn1 (TlsSocket endpoint) (Foreign)

authorized :: forall endpoint. TlsSocket endpoint -> Effect Boolean
authorized s = runEffectFn1 authorizedImpl s

foreign import authorizedImpl :: forall endpoint. EffectFn1 (TlsSocket endpoint) (Boolean)

enableTrace :: forall endpoint. TlsSocket endpoint -> Effect Unit
enableTrace s = runEffectFn1 enableTraceImpl s

foreign import enableTraceImpl :: forall endpoint. EffectFn1 (TlsSocket endpoint) (Unit)

encrypted :: forall endpoint. TlsSocket endpoint -> Effect Boolean
encrypted s = runEffectFn1 encryptedImpl s

foreign import encryptedImpl :: forall endpoint. EffectFn1 (TlsSocket endpoint) (Boolean)

exportKeyingMaterial :: forall endpoint. TlsSocket endpoint -> Int -> String -> Effect Buffer
exportKeyingMaterial s length label = runEffectFn3 exportKeyingMaterialImpl s length label

foreign import exportKeyingMaterialImpl :: forall endpoint. EffectFn3 (TlsSocket endpoint) (Int) (String) (Buffer)

exportKeyingMaterial' :: forall endpoint. TlsSocket endpoint -> Int -> String -> Buffer -> Effect Buffer
exportKeyingMaterial' s length label context = runEffectFn4 exportKeyingMaterialOptionsImpl s length label context

foreign import exportKeyingMaterialOptionsImpl :: forall endpoint. EffectFn4 (TlsSocket endpoint) (Int) (String) (Buffer) (Buffer)

getCertificate :: forall endpoint. TlsSocket endpoint -> Effect Foreign
getCertificate s = runEffectFn1 getCertificateImpl s

foreign import getCertificateImpl :: forall endpoint. EffectFn1 (TlsSocket endpoint) Foreign

getCipher :: forall endpoint. TlsSocket endpoint -> Effect CipherObject
getCipher s = runEffectFn1 getCipherImpl s

foreign import getCipherImpl :: forall endpoint. EffectFn1 (TlsSocket endpoint) (CipherObject)

getEphemeralKeyInfo :: forall endpoint. TlsSocket endpoint -> Effect (Either EphemeralKeyInfoDH EphemeralKeyInfoECDH)
getEphemeralKeyInfo s = (runEffectFn1 getEphemeralKeyInfoImpl s) <#> \r ->
  case r.type of
    "DH" -> Left { type: r.type, size: r.size }
    "ECDH" -> Right { type: r.type, name: r.name, size: r.size }
    x -> unsafeCrashWith $ "Impossible. Unexpected type for emphemeral key info: " <> x

-- Note: `name` value might not exist. Depends on `type` value
foreign import getEphemeralKeyInfoImpl :: forall endpoint. EffectFn1 (TlsSocket endpoint) ({ type :: String, name :: String, size :: Int })

getFinished :: forall endpoint. TlsSocket endpoint -> Effect (Maybe Buffer)
getFinished s = map toMaybe $ runEffectFn1 getFinishedImpl s

foreign import getFinishedImpl :: forall endpoint. EffectFn1 (TlsSocket endpoint) (Nullable Buffer)

getPeerCertificate :: forall endpoint. TlsSocket endpoint -> Effect Foreign
getPeerCertificate s = runEffectFn1 getPeerCertificateImpl s

foreign import getPeerCertificateImpl :: forall endpoint. EffectFn1 (TlsSocket endpoint) (Foreign)

getPeerCertificate' :: forall endpoint. TlsSocket endpoint -> Boolean -> Effect Foreign
getPeerCertificate' s detailed = runEffectFn2 getPeerCertificateOptionsImpl s detailed

foreign import getPeerCertificateOptionsImpl :: forall endpoint. EffectFn2 (TlsSocket endpoint) (Boolean) (Foreign)

getPeerFinished :: forall endpoint. TlsSocket endpoint -> Effect (Maybe Buffer)
getPeerFinished s = map toMaybe $ runEffectFn1 getPeerFinishedImpl s

foreign import getPeerFinishedImpl :: forall endpoint. EffectFn1 (TlsSocket endpoint) (Nullable Buffer)

-- | API is provided here but return value is unspecified since `node:crypto` bindings do not yet exist.
getPeerX509Certificate :: forall endpoint. TlsSocket endpoint -> Effect Foreign
getPeerX509Certificate s = runEffectFn1 getPeerX509CertificateImpl s

foreign import getPeerX509CertificateImpl :: forall endpoint. EffectFn1 (TlsSocket endpoint) (Foreign)

getProtocol :: forall endpoint. TlsSocket endpoint -> Effect (Maybe String)
getProtocol s = map toMaybe $ runEffectFn1 getProtocolImpl s

foreign import getProtocolImpl :: forall endpoint. EffectFn1 (TlsSocket endpoint) (Nullable String)

getSession :: forall endpoint. TlsSocket endpoint -> Effect (Maybe Buffer)
getSession s = map toMaybe $ runEffectFn1 getSessionImpl s

foreign import getSessionImpl :: forall endpoint. EffectFn1 (TlsSocket endpoint) (Nullable Buffer)

getSharedSigalgs :: forall endpoint. TlsSocket endpoint -> Effect (Array String)
getSharedSigalgs s = runEffectFn1 getSharedSigalgsImpl s

foreign import getSharedSigalgsImpl :: forall endpoint. EffectFn1 (TlsSocket endpoint) (Array String)

getTLSTicket :: TlsSocket Client -> Effect (Maybe Buffer)
getTLSTicket s = map toMaybe $ runEffectFn1 getTLSTicketImpl s

foreign import getTLSTicketImpl :: EffectFn1 (TlsSocket Client) (Nullable Buffer)

-- | API is provided here but return value is unspecified since `node:crypto` bindings do not yet exist.
getX509Certificate :: forall endpoint. TlsSocket endpoint -> Effect Foreign
getX509Certificate s = runEffectFn1 getX509CertificateImpl s

foreign import getX509CertificateImpl :: forall endpoint. EffectFn1 (TlsSocket endpoint) (Foreign)

isSessionReused :: forall endpoint. TlsSocket endpoint -> Effect Boolean
isSessionReused s = runEffectFn1 isSessionReusedImpl s

foreign import isSessionReusedImpl :: forall endpoint. EffectFn1 (TlsSocket endpoint) (Boolean)

setMaxSendFragment :: forall endpoint. TlsSocket endpoint -> Int -> Effect Boolean
setMaxSendFragment s size = runEffectFn2 setMaxSendFragmentImpl s size

foreign import setMaxSendFragmentImpl :: forall endpoint. EffectFn2 (TlsSocket endpoint) (Int) (Boolean)

-- connect function

