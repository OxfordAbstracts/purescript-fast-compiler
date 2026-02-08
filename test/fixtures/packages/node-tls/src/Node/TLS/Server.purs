module Node.TLS.Server
  ( toTcpServer
  , createServer
  , createServer'
  , keylogHandle
  , newSessionHandle
  , ocspRequestHandle
  , resumeSessionHandle
  , secureConnectionHandle
  , tlsClientErrorHandle
  , addContext
  , getTicketKeys
  , setSecureContext
  , setTicketKeys
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Nullable (Nullable, notNull, null)
import Effect (Effect)
import Effect.Exception (Error)
import Effect.Uncurried (EffectFn1, EffectFn2, EffectFn3, mkEffectFn1, mkEffectFn2, mkEffectFn3, runEffectFn1, runEffectFn2, runEffectFn3)
import Node.Buffer (Buffer)
import Node.EventEmitter (EventHandle(..))
import Node.EventEmitter.UtilTypes (EventHandle2, EventHandle3, EventHandle1)
import Node.Net.Types as NetTypes
import Node.TLS.Types (CreateSecureContextOptions, Server, TlsCreateServerOptions, TlsServer, TlsSocket)
import Prim.Row as Row
import Unsafe.Coerce (unsafeCoerce)

toTcpServer :: TlsServer -> NetTypes.Server NetTypes.TCP
toTcpServer = unsafeCoerce

foreign import createServer :: Effect (TlsServer)

createServer'
  :: forall r trash
   . Row.Union r trash (TlsCreateServerOptions Server (CreateSecureContextOptions (NetTypes.NewServerOptions ())))
  => { | r }
  -> Effect (TlsServer)
createServer' r = runEffectFn1 createServerOptionsImpl r

foreign import createServerOptionsImpl :: forall r. EffectFn1 { | r } (TlsServer)

keylogHandle :: forall endpoint. EventHandle2 TlsServer Buffer (TlsSocket endpoint)
keylogHandle = EventHandle "keylog" \cb -> mkEffectFn2 \a b -> cb a b

newSessionHandle :: EventHandle3 TlsServer Buffer Buffer (Effect Unit)
newSessionHandle = EventHandle "newSession" \cb -> mkEffectFn3 \a b c -> cb a b c

ocspRequestHandle
  :: EventHandle
       TlsServer
       (Buffer -> (Maybe (Either Error Buffer) -> Effect Unit) -> Effect Unit)
       (EffectFn2 Buffer (EffectFn2 (Nullable Error) (Nullable Buffer) Unit) Unit)
ocspRequestHandle = EventHandle "ocspRequest" \cb ->
  mkEffectFn2 \buff cb' ->
    cb buff $ case _ of
      Nothing -> runEffectFn2 cb' null null
      Just x -> case x of
        Left err -> runEffectFn2 cb' (notNull err) null
        Right buff' -> runEffectFn2 cb' null (notNull buff')

resumeSessionHandle
  :: EventHandle
       TlsServer
       (Buffer -> (Either Error Buffer -> Effect Unit) -> Effect Unit)
       (EffectFn2 Buffer (EffectFn2 (Nullable Error) (Nullable Buffer) Unit) Unit)
resumeSessionHandle = EventHandle "resumeSession" \cb ->
  mkEffectFn2 \buff cb' ->
    cb buff $ case _ of
      Left err -> runEffectFn2 cb' (notNull err) null
      Right buff' -> runEffectFn2 cb' null (notNull buff')

secureConnectionHandle :: forall endpoint. EventHandle1 TlsServer (TlsSocket endpoint)
secureConnectionHandle = EventHandle "secureConnection" mkEffectFn1

tlsClientErrorHandle :: forall endpoint. EventHandle2 TlsServer Error (TlsSocket endpoint)
tlsClientErrorHandle = EventHandle "tlsClientError" \cb -> mkEffectFn2 \a b -> cb a b

addContext
  :: forall r trash
   . Row.Union r trash (CreateSecureContextOptions ())
  => TlsServer
  -> String
  -> { | r }
  -> Effect Unit
addContext s hostname o = runEffectFn3 addContextImpl s hostname o

foreign import addContextImpl :: forall r. EffectFn3 (TlsServer) (String) ({ | r }) (Unit)

getTicketKeys :: TlsServer -> Effect Buffer
getTicketKeys s = runEffectFn1 getTicketKeysImpl s

foreign import getTicketKeysImpl :: EffectFn1 (TlsServer) (Buffer)

setSecureContext
  :: forall r trash
   . Row.Union r trash (CreateSecureContextOptions ())
  => TlsServer
  -> { | r }
  -> Effect Unit
setSecureContext s o = runEffectFn2 setSecureContextImpl s o

foreign import setSecureContextImpl :: forall r. EffectFn2 (TlsServer) ({ | r }) (Unit)

setTicketKeys :: TlsServer -> Buffer -> Effect Unit
setTicketKeys t b = runEffectFn2 setTicketKeysImpl t b

foreign import setTicketKeysImpl :: EffectFn2 (TlsServer) (Buffer) (Unit)
