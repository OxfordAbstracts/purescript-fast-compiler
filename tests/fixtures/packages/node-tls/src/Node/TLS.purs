module Node.TLS
  ( checkServerIdentity
  , createSecureContext
  , createSecureContext'
  , getCiphers
  , rootCertificates
  , defaultEcdhCurve
  , defaultMinVersion
  , defaultMaxVersion
  ) where

import Prelude

import Data.Maybe (Maybe)
import Data.Nullable (Nullable, toMaybe)
import Effect (Effect)
import Effect.Exception (Error)
import Effect.Uncurried (EffectFn1, EffectFn2, runEffectFn1, runEffectFn2)
import Foreign (Foreign)
import Node.TLS.Types (CreateSecureContextOptions, SecureContext)
import Prim.Row as Row

checkServerIdentity :: String -> Foreign -> Effect (Maybe Error)
checkServerIdentity hostname cert = map toMaybe $ runEffectFn2 checkServerIdentityImpl hostname cert

foreign import checkServerIdentityImpl :: EffectFn2 (String) (Foreign) (Nullable Error)

foreign import createSecureContext :: Effect (SecureContext)

createSecureContext'
  :: forall r trash
   . Row.Union r trash (CreateSecureContextOptions ())
  => { | r }
  -> Effect SecureContext
createSecureContext' o = runEffectFn1 createSecureContextOptionsImpl o

foreign import createSecureContextOptionsImpl :: forall r. EffectFn1 ({ | r }) (SecureContext)

foreign import getCiphers :: Effect (Array String)

foreign import rootCertificates :: Array String

foreign import defaultEcdhCurve :: String
foreign import defaultMinVersion :: String
foreign import defaultMaxVersion :: String
foreign import defaultCiphers :: String
