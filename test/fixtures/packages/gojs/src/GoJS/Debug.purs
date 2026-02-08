module GoJS.Debug where

import Prelude

import Effect (Effect)

-- gets around type system, like Debug.Trace
foreign import trace :: forall a. a -> a
foreign import ffilog :: forall a. a -> Effect Unit