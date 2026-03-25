module MyState where

-- Simplified MonadState pattern through type alias + newtype

class MyMonad m where
  myPure :: forall a. a -> m a

data MyIdentity a = MyIdentity a

instance myMonadIdentity :: MyMonad MyIdentity where
  myPure a = MyIdentity a

-- StateT-like newtype
newtype MyStateT s m a = MyStateT (s -> m { state :: s, value :: a })

-- MonadState-like class
class MyMonadState s m where
  myState :: forall a. (s -> { state :: s, value :: a }) -> m a

-- Instance: MonadState s (MyStateT s m) requires MyMonad m
instance myMonadStateMyStateT :: MyMonad m => MyMonadState s (MyStateT s m) where
  myState f = MyStateT (\s -> myPure (f s))

-- Type alias: MyState = MyStateT with Identity
type MyState s = MyStateT s MyIdentity

-- Unwrap helper
runMyState :: forall s a. MyState s a -> s -> { state :: s, value :: a }
runMyState (MyStateT f) s = case f s of
  MyIdentity r -> r
