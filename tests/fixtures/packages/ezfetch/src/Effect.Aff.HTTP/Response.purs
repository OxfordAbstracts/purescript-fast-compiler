module Effect.Aff.HTTP.Response
  ( Response(..)
  , stream
  , clone
  , json
  , text
  , blob
  , arrayBuffer
  , formData
  , headers
  , status
  , statusText
  , guardStatusOk
  ) where

import Prelude

import Control.Monad.Error.Class (class MonadThrow, liftEither, throwError)
import Control.Monad.Except (runExcept)
import Control.Promise (Promise)
import Control.Promise as Promise
import Data.ArrayBuffer.Types (ArrayBuffer, ArrayView, Uint8)
import Data.Bifunctor (lmap)
import Data.Int as Int
import Data.Map (Map)
import Data.Map as Map
import Data.Number ((%))
import Effect (Effect)
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Exception (Error, error)
import Foreign (Foreign)
import Foreign.Object (Object)
import Effect.Aff.HTTP.Form (Form, RawFormData)
import Effect.Aff.HTTP.Form as Form
import Simple.JSON (class ReadForeign, readImpl)
import Web.File.Blob (Blob)
import Web.Streams.ReadableStream (ReadableStream)

foreign import data Response :: Type

foreign import cloneImpl :: Response -> Effect Response
foreign import statusImpl :: Response -> Effect Int
foreign import statusTextImpl :: Response -> Effect String
foreign import headersImpl :: Response -> Effect (Object String)
foreign import jsonImpl :: Response -> Effect (Promise Foreign)
foreign import textImpl :: Response -> Effect (Promise String)
foreign import abImpl :: Response -> Effect (Promise ArrayBuffer)
foreign import blobImpl :: Response -> Effect (Promise Blob)
foreign import formImpl :: Response -> Effect (Promise RawFormData)
foreign import streamImpl :: Response -> Effect (ReadableStream (ArrayView Uint8))

guardStatusOk :: forall m. MonadAff m => MonadThrow Error m => Response -> m Unit
guardStatusOk rep = do
  status' <- status rep
  statusText' <- statusText rep
  if Int.toNumber status' % 200.0 > 100.0 then
    throwError $ error $ "status not OK: " <> show status' <> " " <> statusText'
  else
    pure unit

clone :: forall m. MonadEffect m => Response -> m Response
clone = liftEffect <<< cloneImpl

json :: forall m @a. MonadAff m => ReadForeign a => Response -> m a
json = liftAff <<< flip bind (liftEither <<< lmap (error <<< show) <<< runExcept <<< readImpl) <<< Promise.toAffE <<< jsonImpl

text :: forall m. MonadAff m => Response -> m String
text = liftAff <<< Promise.toAffE <<< textImpl

blob :: forall m. MonadAff m => Response -> m Blob
blob = liftAff <<< Promise.toAffE <<< blobImpl

stream :: forall m. MonadEffect m => Response -> m (ReadableStream (ArrayView Uint8))
stream = liftEffect <<< streamImpl

arrayBuffer :: forall m. MonadAff m => Response -> m ArrayBuffer
arrayBuffer = liftAff <<< Promise.toAffE <<< abImpl

formData :: forall m. MonadAff m => Response -> m Form
formData = liftAff <<< flip bind Form.fromRaw <<< Promise.toAffE <<< formImpl

headers :: forall m. MonadEffect m => Response -> m (Map String String)
headers = liftEffect <<< map Map.fromFoldableWithIndex <<< headersImpl

status :: forall m. MonadEffect m => Response -> m Int
status = liftEffect <<< statusImpl

statusText :: forall m. MonadEffect m => Response -> m String
statusText = liftEffect <<< statusTextImpl
