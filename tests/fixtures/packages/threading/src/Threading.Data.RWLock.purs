-- | A RWLock allows threads to share mutable state.
-- |
-- | Any number of threads can concurrently read the state,
-- | when there isn't a thread with write access.
-- |
-- | Get write access with `lockWrite` or `tryLockWrite`,
-- | or read access with `lockRead` or `tryLockRead`.
-- |
-- | `(try)lockWrite` returns a `WriteGuard`, which guarantees
-- | no other threads have read or write access until it is released.
-- |
-- | `(try)lockRead` returns a `ReadGuard`, which guarantees
-- | no threads have write access until it is released.
module Threading.Data.RWLock
  ( RWLock
  , ReadGuard
  , WriteGuard
  , rwLock
  , lockWrite
  , tryLockWrite
  , lockRead
  , tryLockRead
  , locked
  , Locked(..)
  , get
  , put
  , modify
  , modify_
  , release
  , read
  , write
  , class RWLockGuard
  ) where

import Prelude

import Control.Alternative (guard)
import Control.Monad.Error.Class (liftMaybe, throwError)
import Control.Monad.Maybe.Trans (runMaybeT)
import Control.Monad.Trans.Class (lift)
import Data.Foldable (elem, traverse_)
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Show.Generic (genericShow)
import Data.Traversable (traverse)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (error)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Threading.Data.Mutex (Mutex)
import Threading.Data.Mutex as Mutex
import Type.Function (type ($))

-- | The lock state of the RWLock
data Locked
  -- | There are no readers or writers.
  = Unlocked
  -- | There is a writer, and the RWLock is not
  -- | currently readable or writable.
  | LockedWriting
  -- | There is at least one reader, and the RWLock is not
  -- | currently writable.
  | LockedReading

derive instance Generic Locked _
derive instance Eq Locked
instance Show Locked where
  show = genericShow

newtype WriteLockHeld = WriteLockHeld (Maybe Int)

-- | A Read-Write lock
-- |
-- | Ensures that there can be at most 1 thread with write
-- | access to the data contained in the RWLock, or any
-- | number of concurrent readers.
data RWLock a = RWLock
  -- Guarantee that state transitions are exclusive
  { fence :: Mutex Unit
  -- Monotonically increasing guard counter
  , id :: Ref Int
  -- Condvar-style mutex indicating writability.
  --
  -- When a lock is held and the mutex contains `WriteLockHeld Nothing`, then there are 1 or more readers.
  --
  -- When a lock is held and the mutex contains `WriteLockHeld (Just <id>)`, then the lock is held by a writer.
  , w :: Mutex WriteLockHeld
  -- Ref containing the MutexGuard for `w`.
  --
  -- When a held WriteGuard or the final held ReadGuard is released, the guard contained will be
  -- released, and `Nothing` will be written here.
  , wLock :: Ref $ Maybe $ Mutex.Guard WriteLockHeld
  -- Ref tracking active readers
  , readers :: Mutex $ Set Int
  -- The data contained in the RWLock
  , state :: Ref a
  }

-- | Internal
-- |
-- | Guarantees that no other `fenced` sections
-- | run concurrently with this one.
fenced :: forall a r. RWLock a -> Aff r -> Aff r
fenced (RWLock { fence }) m = do
  g <- Mutex.lock fence
  m <* liftEffect (Mutex.release g)

-- | A guard with read access to data of type `a`
data ReadGuard a = ReadGuard Int (RWLock a)

-- | A guard with read+write access to data of type `a`
data WriteGuard a = WriteGuard Int (RWLock a)

-- | Acquire a write-access lock to the data
-- | contained in the RWLock.
-- |
-- | If another thread holds a `ReadGuard` or `WriteGuard`,
-- | this will block until the data is writable.
lockWrite :: forall a. RWLock a -> Aff (WriteGuard a)
lockWrite rw@(RWLock { id: idRef, w, wLock }) = do
  id <- liftEffect $ Ref.modify (_ + 1) idRef
  g <- Mutex.lock w
  liftEffect $ Mutex.write g $ WriteLockHeld $ Just id
  liftEffect $ Ref.write (Just g) wLock
  pure $ WriteGuard id rw

-- | Acquire a write-access lock to the data
-- | contained in the RWLock.
-- |
-- | If another thread holds a `ReadGuard` or `WriteGuard`,
-- | this will return Nothing.
tryLockWrite :: forall a. RWLock a -> Aff (Maybe (WriteGuard a))
tryLockWrite rw =
  fenced rw
    $ liftEffect (locked rw) >>= case _ of
        Unlocked -> Just <$> lockWrite rw
        _ -> pure Nothing

-- | Acquire a read-access lock to the data
-- | contained in the RWLock.
-- |
-- | If another thread holds a `WriteGuard`,
-- | this will block until the data is readable.
lockRead :: forall a. RWLock a -> Aff (ReadGuard a)
lockRead rw@(RWLock { fence, id: idRef, w, wLock, readers: readersM }) = do
  fenceG <- Mutex.lock fence
  id <- liftEffect $ Ref.modify (_ + 1) idRef
  l <- liftEffect $ locked rw
  let
    block = do
      wl' <- Mutex.lock w
      liftEffect $ Mutex.write wl' (WriteLockHeld Nothing)
      liftEffect $ Ref.write (Just wl') wLock
    done = liftEffect (Mutex.release fenceG)

  fenceG' <- case l of
    LockedReading -> pure fenceG
    LockedWriting -> done *> block *> Mutex.lock fence
    Unlocked -> block $> fenceG

  readersG <- Mutex.lock readersM
  liftEffect do
    readers <- Mutex.read readersG
    Mutex.write readersG $ Set.insert id readers
    Mutex.release readersG
    Mutex.release fenceG'
  pure $ ReadGuard id rw

-- | Acquire a read-access lock to the data
-- | contained in the RWLock.
-- |
-- | If another thread holds a `WriteGuard`,
-- | this will return Nothing.
tryLockRead :: forall a. RWLock a -> Aff (Maybe (ReadGuard a))
tryLockRead rw =
  liftEffect (locked rw) >>= case _ of
      LockedWriting -> pure Nothing
      _ -> Just <$> lockRead rw

-- | Create a new RWLock
rwLock :: forall a. a -> Effect (RWLock a)
rwLock a = do
  fence <- Mutex.mutex unit
  id <- liftEffect $ Ref.new 0
  w <- Mutex.mutex $ WriteLockHeld Nothing
  wLock <- liftEffect $ Ref.new Nothing
  readers <- Mutex.mutex Set.empty
  state <- liftEffect $ Ref.new a
  pure $ RWLock { fence, id, w, wLock, readers, state }

-- | Typeclass implemented by `WriteGuard` and `ReadGuard`
-- | allowing a common `release` + `read` function (as opposed
-- | to `releaseRead`, `releaseWrite`, etc.)
class RWLockGuard g where
  release :: forall a. g a -> Aff Unit
  read :: forall a. g a -> Aff a

instance RWLockGuard WriteGuard where
  release w@(WriteGuard _ rw@(RWLock { wLock })) =
    fenced rw $ void $ liftEffect do
      g <- _writeGuardOk w
      Ref.write Nothing wLock
      Mutex.release g
  read (WriteGuard id rw@(RWLock { state, wLock })) =
    fenced rw $ liftEffect do
      mg <- Ref.read wLock
      g <- liftMaybe (error "WriteGuard has been released!") mg
      WriteLockHeld id' <- Mutex.read g
      when (Just id /= id') $ throwError $ error "WriteGuard has been released!"
      Ref.read state

instance RWLockGuard ReadGuard where
  release (ReadGuard id rw@(RWLock { wLock, readers: readersM })) =
    fenced rw $ void $ runMaybeT do
      readersG <- lift $ Mutex.lock readersM
      readers <- liftEffect $ Mutex.read readersG
      guard $ elem id readers
      liftEffect do
        Mutex.write readersG $ Set.delete id readers
        empty <- ((_ == 0) <<< Set.size) <$> Mutex.read readersG
        Mutex.release readersG
        when empty $ Ref.read wLock >>= traverse_ \g -> do
          Ref.write Nothing wLock
          Mutex.release g
  read (ReadGuard id rw@(RWLock { readers: readersM, state })) =
    fenced rw do
      readersG <- Mutex.lock readersM
      readers <- liftEffect $ Mutex.read readersG
      when (not $ elem id readers) $ throwError $ error "ReadGuard has been released!"
      liftEffect $ Mutex.release readersG
      liftEffect $ Ref.read state

_writeGuardOk :: forall a. WriteGuard a -> Effect (Mutex.Guard WriteLockHeld)
_writeGuardOk (WriteGuard id (RWLock { wLock })) = do
  mg <- Ref.read wLock
  g <- liftMaybe (error "WriteGuard has been released!") mg
  WriteLockHeld id' <- Mutex.read g
  when (Just id /= id') $ throwError $ error "WriteGuard has been released!"
  pure g

-- | Writes a new value
write :: forall a. WriteGuard a -> a -> Effect Unit
write w@(WriteGuard _ (RWLock { state })) a = do
  void $ _writeGuardOk w
  Ref.write a state

-- | Asks what state the RWLock is currently in
locked :: forall a. RWLock a -> Effect Locked
locked (RWLock { wLock }) = do
  Ref.read wLock
    >>= traverse Mutex.read
    >>= case _ of
      Nothing -> pure Unlocked
      Just (WriteLockHeld Nothing) -> pure LockedReading
      Just (WriteLockHeld (Just _)) -> pure LockedWriting

-- | Get the value currently in the RWLock.
-- |
-- | Shorthand for `lockRead rw >>= (\l -> read l <* release l)`
get :: forall a. RWLock a -> Aff a
get rw = lockRead rw >>= (\l -> read l <* release l)

-- | Write a new value to the RWLock.
-- |
-- | Shorthand for `lockWrite rw >>= (\l -> liftEffect (write l a) <* release l)`
put :: forall a. RWLock a -> a -> Aff Unit
put rw a = lockWrite rw >>= (\l -> liftEffect (write l a) <* release l)

-- | Modify the value in the RWLock using the provided function.
modify :: forall a. RWLock a -> (a -> a) -> Aff a
modify rw f = do
  l <- lockWrite rw
  a <- f <$> read l
  liftEffect (write l a) *> release l $> a

-- | Shorthand for `void $ modify rw f`
modify_ :: forall a. RWLock a -> (a -> a) -> Aff Unit
modify_ rw f = void $ modify rw f
