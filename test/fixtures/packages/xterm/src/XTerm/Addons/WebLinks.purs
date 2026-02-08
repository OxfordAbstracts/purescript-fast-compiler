module XTerm.Addons.WebLinks where

import Effect (Effect)
import Unsafe.Coerce (unsafeCoerce)
import XTerm.Disposable (class IsDisposable)

data WebLinksAddon

foreign import webLinksAddon :: Effect WebLinksAddon 

instance IsDisposable WebLinksAddon where
  toDisposable = unsafeCoerce


