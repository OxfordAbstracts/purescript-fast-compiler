module MyTrans where

import Prelude

-- A simple transformer: wraps another functor
newtype MyTrans m a = MyTrans (m a)

instance functorMyTrans :: Functor m => Functor (MyTrans m) where
  map f (MyTrans ma) = MyTrans (map f ma)

unMyTrans :: forall m a. MyTrans m a -> m a
unMyTrans (MyTrans ma) = ma
