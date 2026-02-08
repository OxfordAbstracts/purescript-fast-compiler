-- | A Mutex allows any number of threads to share mutable
-- | state, with at most 1 thread having read or write access
-- | at a time.
-- |
-- | Threads can access the data with `lock` or `tryLock`,
-- | which both return a `Guard`.
-- |
-- | The holder of a `Guard` is guaranteed exclusive read &
-- | write access to the data contained in the `Mutex`.
module Threading.Data.Mutex
  ( Mutex
  , Guard
  , mutex
  , lock
  , tryLock
  , locked
  , release
  , modify
  , modify_
  , write
  , read
  , get
  , put
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Nullable (Nullable)
import Data.Nullable as Nullable
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff as Aff
import Effect.Class (liftEffect)

foreign import data Waker :: Type

foreign import data Mutex :: Type -> Type

-- | A lock to a Mutex.
-- |
-- | Guards may be read from, written to, and released. Guards **must** be
-- | released in order for other blocking threads to continue.
-- |
-- | _Note: If a Guard reclaimed by the garbage collector without being released,
-- | its Mutex will notice and behave as if the Guard was explicitly released.
-- | This will hopefully catch deadlocks caused by threads that have exited
-- | while holding a Guard._
foreign import data Guard :: Type -> Type

foreign import _make :: forall a. a -> Effect (Mutex a)

foreign import _locked :: forall a. Mutex a -> Effect Boolean
foreign import _lock :: forall a. Mutex a -> (Guard a -> Effect Unit) -> Effect (Nullable Waker)
foreign import _tryLock :: forall a. Mutex a -> Effect (Nullable (Guard a))

foreign import _releaseWaker :: forall a. Mutex a -> Waker -> Effect Unit

foreign import _guardRead :: forall a. Guard a -> Effect a
foreign import _guardWrite :: forall a. Guard a -> a -> Effect Unit
foreign import _guardRelease :: forall a. Guard a -> Effect Unit

-- | Create a new Mutex
mutex :: forall a. a -> Effect (Mutex a)
mutex = _make

-- | Is the Mutex currently locked?
locked :: forall a. Mutex a -> Effect Boolean
locked = _locked

-- | Attempt to acquire a lock without blocking.
-- |
-- | If the Mutex is currently locked, this will return `Nothing`.
tryLock :: forall a. Mutex a -> Effect (Maybe (Guard a))
tryLock = map Nullable.toMaybe <<< _tryLock

-- | Acquire a lock, blocking if another thread
-- | currently holds a lock.
-- |
-- | If multiple threads invoke `lock`, they will
-- | be unlocked in the order that they blocked on `lock`.
lock :: forall a. Mutex a -> Aff (Guard a)
lock m = Aff.makeAff \cb -> do
  waker <- Nullable.toMaybe <$> _lock m (cb <<< Right)
  pure $ case waker of
    Just w -> Aff.effectCanceler $ _releaseWaker m w
    Nothing -> Aff.nonCanceler

-- | Take a snapshot of the value in a Mutex
-- |
-- | This is a shorthand for acquiring a lock, reading it,
-- | then immediately releasing the lock.
get :: forall a. Mutex a -> Aff a
get m = do
  g <- lock m
  a <- liftEffect $ read g <* release g
  pure a

-- | Write a new value to a Mutex
-- |
-- | This is a shorthand for acquiring a lock, writing to it,
-- | then immediately releasing the lock.
put :: forall a. Mutex a -> a -> Aff Unit
put m a = do
  g <- lock m
  liftEffect $ write g a *> release g

-- | Modify the value contained in a Mutex
-- |
-- | This is a shorthand for acquiring a lock,
-- | reading from it, writing to it, then
-- | immediately releasing it.
-- |
-- | Returns the new value.
modify :: forall a. Mutex a -> (a -> a) -> Aff a
modify m f = do
  g <- lock m
  liftEffect $ ((f <$> read g) >>= (\a -> write g a *> release g $> a))

-- | `modify` with its return value ignored.
modify_ :: forall a. Mutex a -> (a -> a) -> Aff Unit
modify_ m f = void $ modify m f

-- | Release the lock
-- |
-- | Attempting to `read` or `write` this `Guard`
-- | will throw an exception.
-- |
-- | Repeated invocations of `release` are ignored.
release :: forall a. Guard a -> Effect Unit
release = _guardRelease

-- | Read the value in the Mutex via the Guard
read :: forall a. Guard a -> Effect a
read = _guardRead

-- | Write a new value into the Mutex via the Guard
write :: forall a. Guard a -> a -> Effect Unit
write = _guardWrite
