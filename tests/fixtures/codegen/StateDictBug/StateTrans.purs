module StateTrans where

import Prelude
import Data.Newtype (class Newtype)

-- Simplified StateT, mirroring Control.Monad.State.Trans
newtype StateT s m a = StateT (s -> m { value :: a, state :: s })

derive instance newtypeStateT :: Newtype (StateT s m a) _

instance functorStateT :: Monad m => Functor (StateT s m) where
  map f (StateT k) = StateT \s -> do
    r <- k s
    pure { value: f r.value, state: r.state }

instance applyStateT :: Monad m => Apply (StateT s m) where
  apply (StateT f) (StateT x) = StateT \s -> do
    rf <- f s
    rx <- x rf.state
    pure { value: rf.value rx.value, state: rx.state }

instance applicativeStateT :: Monad m => Applicative (StateT s m) where
  pure a = StateT \s -> pure { value: a, state: s }

instance bindStateT :: Monad m => Bind (StateT s m) where
  bind (StateT k) f = StateT \s -> do
    r <- k s
    let StateT g = f r.value
    g r.state

instance monadStateT :: Monad m => Monad (StateT s m)

-- MonadState class
class Monad m <= MonadState s m | m -> s where
  state :: forall a. (s -> { value :: a, state :: s }) -> m a

instance monadStateStateT :: Monad m => MonadState s (StateT s m) where
  state f = StateT (pure <<< f)

-- Type alias like Control.Monad.State.State
type State s = StateT s Identity

-- Run functions
runState :: forall s a. State s a -> s -> { value :: a, state :: s }
runState (StateT f) s = let Identity r = f s in r

-- Identity (simplified, since it might not be in scope)
newtype Identity a = Identity a

derive instance newtypeIdentity :: Newtype (Identity a) _

instance functorIdentity :: Functor Identity where
  map f (Identity a) = Identity (f a)

instance applyIdentity :: Apply Identity where
  apply (Identity f) (Identity a) = Identity (f a)

instance applicativeIdentity :: Applicative Identity where
  pure = Identity

instance bindIdentity :: Bind Identity where
  bind (Identity a) f = f a

instance monadIdentity :: Monad Identity
