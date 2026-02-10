module Effect.Aff.HTTP.Header where

import Prelude

import Control.Monad.Error.Class (liftEither)
import Data.Eq.Generic (genericEq)
import Data.Generic.Rep (class Generic)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe, maybe)
import Data.Newtype (class Newtype, unwrap, wrap)
import Data.Show.Generic (genericShow)
import Data.String.Base64 as String.Base64
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Class (class MonadEffect, liftEffect)
import Data.MIME (MIME)
import Data.MIME as MIME

newtype ContentType = ContentType MIME

derive instance Newtype ContentType _
derive newtype instance Show ContentType
derive newtype instance Eq ContentType

newtype Accept = Accept MIME

derive instance Newtype Accept _
derive newtype instance Show Accept
derive newtype instance Eq Accept

newtype AuthScheme = AuthScheme String

derive instance Newtype AuthScheme _
derive newtype instance Show AuthScheme
derive newtype instance Eq AuthScheme
derive newtype instance Ord AuthScheme

data Authorization
  = AuthBasic { username :: String, password :: String }
  | AuthBearer String
  | AuthCustom AuthScheme String

derive instance Generic Authorization _
instance Show Authorization where
  show = genericShow

instance Eq Authorization where
  eq = genericEq

authorizationValue :: forall m. MonadEffect m => Authorization -> m String
authorizationValue (AuthBasic { username, password }) = do
  val <- liftEffect $ liftEither $ String.Base64.btoa $ username <> ":" <> password
  authorizationValue $ AuthCustom (wrap "Basic") val
authorizationValue (AuthBearer val) = authorizationValue $ AuthCustom (wrap "Bearer") val
authorizationValue (AuthCustom (AuthScheme scheme) val) = pure $ scheme <> " " <> val

newtype Headers = Headers (Map String String)

derive instance Newtype Headers _
derive newtype instance Eq Headers
derive newtype instance Ord Headers
derive newtype instance Show Headers
instance Semigroup Headers where
  append (Headers amap) (Headers bmap) = wrap $ Map.union amap bmap

instance Monoid Headers where
  mempty = wrap $ Map.empty

class IntoHeaders a where
  headers :: a -> Effect Headers

instance IntoHeaders Headers where
  headers = pure
else instance IntoHeaders (Map String String) where
  headers = pure <<< wrap
else instance IntoHeaders (Tuple String String) where
  headers (Tuple k v) = headers $ Map.singleton k v
else instance IntoHeaders Unit where
  headers _ = pure $ wrap Map.empty
else instance IntoHeaders ContentType where
  headers = headers <<< Map.singleton "Content-Type" <<< MIME.toString <<< unwrap
else instance IntoHeaders Accept where
  headers = headers <<< Map.singleton "Accept" <<< MIME.toString <<< unwrap
else instance IntoHeaders Authorization where
  headers = map wrap <<< map (Map.singleton "Authorization") <<< authorizationValue
else instance (IntoHeaders a, IntoHeaders b) => IntoHeaders (Tuple a b) where
  headers (Tuple a b) = do
    a' <- unwrap <$> headers a
    b' <- unwrap <$> headers b
    headers $ Map.union a' b'
else instance IntoHeaders a => IntoHeaders (Maybe a) where
  headers = maybe (pure mempty) headers
