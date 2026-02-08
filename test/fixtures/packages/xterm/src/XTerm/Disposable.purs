module XTerm.Disposable
  ( Disposable
  , class IsDisposable
  , toDisposable
  , class Dispose
  , dispose
  ) where

import Control.Category (identity, (<<<))
import Data.Unit (Unit)
import Effect (Effect)

data Disposable

class IsDisposable a where
  toDisposable :: a -> Disposable

instance IsDisposable Disposable where
  toDisposable = identity

class Dispose a where
  dispose :: a -> Effect Unit

instance IsDisposable a => Dispose a where
  dispose = _dispose <<< toDisposable

foreign import _dispose :: Disposable -> Effect Unit

