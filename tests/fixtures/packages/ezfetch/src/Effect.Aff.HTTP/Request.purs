module Effect.Aff.HTTP.Request
  ( Credentials(..)
  , Body(..)
  , RawBody
  , Method(..)
  , bodyHeaders
  , bodyToRaw
  , json
  , form
  , blob
  , arrayBuffer
  , rawBodySize
  ) where

import Prelude

import Control.Promise (Promise)
import Control.Promise as Promise
import Data.ArrayBuffer.Types (ArrayBuffer)
import Data.Eq.Generic (genericEq)
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.Show.Generic (genericShow)
import Effect (Effect)
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Aff.HTTP.Form (Form, RawFormData)
import Effect.Aff.HTTP.Form as Form
import Effect.Aff.HTTP.Header (ContentType(..), Headers)
import Effect.Aff.HTTP.Header as Header
import Data.MIME (MIME)
import Data.MIME as MIME
import Simple.JSON (class WriteForeign, writeJSON)
import Unsafe.Coerce (unsafeCoerce)
import Web.File.Blob (Blob)
import Web.File.Blob as Blob

foreign import data RawBody :: Type

foreign import blobArrayBufferImpl :: Blob -> Effect (Promise ArrayBuffer)
foreign import rawBodySize :: RawBody -> Effect Int

unsafeStringRawBody :: String -> RawBody
unsafeStringRawBody = unsafeCoerce

unsafeFormDataToRawBody :: RawFormData -> RawBody
unsafeFormDataToRawBody = unsafeCoerce

unsafeArrayBufferToRawBody :: ArrayBuffer -> RawBody
unsafeArrayBufferToRawBody = unsafeCoerce

unsafeBlobToRawBody :: forall m. MonadAff m => Blob -> m RawBody
unsafeBlobToRawBody = map unsafeArrayBufferToRawBody <<< liftAff <<< Promise.toAffE <<< blobArrayBufferImpl

data Credentials
  = IncludeCredentials
  | OmitCredentials
  | SameSiteCredentials

data Body
  = BodyString String (Maybe ContentType)
  | BodyArrayBuffer ArrayBuffer (Maybe ContentType)
  | BodyBlob Blob
  | BodyForm Form
  | BodyEmpty

json :: forall a. WriteForeign a => a -> Body
json = flip BodyString (Just $ ContentType MIME.Json) <<< writeJSON

form :: Form -> Body
form = BodyForm

blob :: Blob -> Body
blob = BodyBlob

arrayBuffer :: MIME -> ArrayBuffer -> Body
arrayBuffer mime buf = BodyArrayBuffer buf $ Just $ ContentType mime

bodyHeaders :: forall m. MonadEffect m => Body -> m Headers
bodyHeaders (BodyForm _) = pure mempty
bodyHeaders (BodyEmpty) = pure mempty
bodyHeaders (BodyString _ ct) = liftEffect $ Header.headers ct
bodyHeaders (BodyArrayBuffer _ ct) = liftEffect $ Header.headers ct
bodyHeaders (BodyBlob b) = liftEffect $ Header.headers <<< map (ContentType <<< MIME.fromString <<< unwrap) $ Blob.type_ b

bodyToRaw :: forall m. MonadAff m => Body -> m (Maybe RawBody)
bodyToRaw (BodyString body _) = pure $ Just $ unsafeStringRawBody body
bodyToRaw (BodyArrayBuffer body _) = pure $ Just $ unsafeArrayBufferToRawBody body
bodyToRaw (BodyForm form') = map Just $ map unsafeFormDataToRawBody $ Form.toRawFormData form'
bodyToRaw (BodyBlob body) = map Just $ unsafeBlobToRawBody body
bodyToRaw BodyEmpty = pure Nothing

data Method
  = GET
  | PUT
  | POST
  | DELETE
  | PATCH
  | HEAD

derive instance Generic Method _
instance Eq Method where
  eq = genericEq

instance Show Method where
  show = genericShow

