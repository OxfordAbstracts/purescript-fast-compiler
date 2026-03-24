-- A simple monad transformer-like type with a Functor instance.
-- Mirrors Control.Monad.State.Trans.StateT
module MyTrans where

import Prelude

newtype MyTrans m a = MyTrans (m a)

runMyTrans :: forall m a. MyTrans m a -> m a
runMyTrans (MyTrans ma) = ma

instance functorMyTrans :: Functor m => Functor (MyTrans m) where
  map f (MyTrans ma) = MyTrans (map f ma)
