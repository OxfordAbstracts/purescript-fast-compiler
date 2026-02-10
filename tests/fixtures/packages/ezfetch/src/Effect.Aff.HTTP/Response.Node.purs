module Effect.Aff.HTTP.Response.Node
  ( module X
  , buffer
  , stream
  ) where

import Prelude

import Control.Promise (Promise)
import Control.Promise as Promise
import Effect (Effect)
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Aff.HTTP.Response (Response)
import Effect.Aff.HTTP.Response hiding (stream) as X
import Node.Buffer (Buffer)
import Node.Stream (Readable)

foreign import bufferImpl :: Response -> Effect (Promise Buffer)
foreign import streamImpl :: Response -> Effect (Readable ())

buffer :: forall m. MonadAff m => Response -> m Buffer
buffer = liftAff <<< Promise.toAffE <<< bufferImpl

stream :: forall m. MonadEffect m => Response -> m (Readable ())
stream = liftEffect <<< streamImpl
