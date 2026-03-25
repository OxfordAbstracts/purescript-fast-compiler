module MyWriter where

-- Simplified MonadTell pattern with TWO constraint parameters

class MySemigroup a where
  myAppend :: a -> a -> a

class MySemigroup a <= MyMonoid a where
  myMempty :: a

class MyMonad m where
  myPure :: forall a. a -> m a

class MyTell w m where
  myTell :: w -> m w

-- Writer-like type (simplified)
newtype MyWriterT w m a = MyWriterT a

-- Instance with TWO constraints: MyMonoid w, MyMonad m
instance myTellWriterT :: (MyMonoid w, MyMonad m) => MyTell w (MyWriterT w m) where
  myTell w = MyWriterT w

-- Concrete instances
instance mySemigroupString :: MySemigroup String where
  myAppend a _ = a

instance myMonoidString :: MyMonoid String where
  myMempty = ""

-- A concrete monad
data MyIdentity a = MyIdentity a

instance myMonadIdentity :: MyMonad MyIdentity where
  myPure a = MyIdentity a

unwrapWriterT :: forall w m a. MyWriterT w m a -> a
unwrapWriterT (MyWriterT a) = a
