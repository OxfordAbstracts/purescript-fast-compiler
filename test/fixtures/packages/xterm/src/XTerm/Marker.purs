module XTerm.Marker where

import Effect (Effect)
import Unsafe.Coerce (unsafeCoerce)
import XTerm.DisposableWithEvent (class IsDisposableWithEvent)

data Marker

instance IsDisposableWithEvent Marker where
  toDisposableWithEvent = unsafeCoerce

foreign import id :: Marker -> Int
foreign import line :: Marker -> Effect Int 
