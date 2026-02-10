module JS.Drop where

import Prelude

import Effect (Effect)
import JS.WeakRef (WeakRef)

type Registry_ a = Registry a Unit

foreign import data Registry :: Type -> Type -> Type

foreign import registry :: forall a b. (b -> Effect Unit) -> Effect (Registry a b)

foreign import register :: forall a b. Registry a b -> WeakRef a -> b -> Effect Unit
foreign import unregister :: forall a b. Registry a b -> WeakRef a -> Effect Unit
