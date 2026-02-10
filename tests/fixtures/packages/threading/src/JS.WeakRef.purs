module JS.WeakRef where

import Prelude

import Data.Maybe (Maybe)
import Data.Nullable (Nullable)
import Data.Nullable as Nullable
import Effect (Effect)

foreign import data WeakRef :: Type -> Type

foreign import make :: forall a. a -> Effect (WeakRef a)

deref :: forall a. WeakRef a -> Effect (Maybe a)
deref = map Nullable.toMaybe <<< _deref

foreign import _deref :: forall a. WeakRef a -> Effect (Nullable a)
