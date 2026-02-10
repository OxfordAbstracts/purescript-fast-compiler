module XTerm.DisposableWithEvent
  ( DisposableWithEvent
  , class IsDisposableWithEvent
  , toDisposableWithEvent
  , class DisposeWithEvent
  , onDispose
  , isDisposed
  ) where

import Control.Category ((<<<))
import Data.Unit (Unit)
import Effect (Effect)
import Unsafe.Coerce (unsafeCoerce)
import XTerm.Disposable (class IsDisposable, Disposable)

data DisposableWithEvent

class IsDisposableWithEvent a where
  toDisposableWithEvent :: a -> DisposableWithEvent

instance IsDisposable DisposableWithEvent where
  toDisposable = unsafeCoerce

class DisposeWithEvent a where
  onDispose :: a -> Effect Unit -> Effect Disposable
  isDisposed :: a -> Effect Boolean

instance IsDisposableWithEvent a => DisposeWithEvent a where
  onDispose a e = _onDispose (toDisposableWithEvent a) e
  isDisposed = _isDisposed <<< toDisposableWithEvent

foreign import _onDispose :: DisposableWithEvent -> Effect Unit -> Effect Disposable
foreign import _isDisposed :: DisposableWithEvent -> Effect Boolean

