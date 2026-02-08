module XTerm.Addons.WebGL where

import Data.Unit (Unit)
import Effect (Effect)
import Unsafe.Coerce (unsafeCoerce)
import XTerm.Disposable (class IsDisposable, Disposable)

data WebGLAddon

foreign import webGLAddon :: Effect WebGLAddon 

foreign import onContextLoss :: WebGLAddon -> Effect Unit -> Effect Disposable

instance IsDisposable WebGLAddon where
  toDisposable = unsafeCoerce


