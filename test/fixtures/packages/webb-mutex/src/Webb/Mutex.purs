module Webb.Mutex where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (class MonadEffect, liftEffect)
import Webb.Mutex.Internal.Mutex as Mutex
import Webb.Mutex.Internal.Mutex.State (MutexState, newMutexState)


newtype Mutex = M MutexState

derive newtype instance Show Mutex

newMutex :: forall m. MonadEffect m => m Mutex
newMutex = liftEffect do
  state <- newMutexState
  pure $ M state

run :: forall a m. MonadAff m => Mutex -> (MutexState -> Aff a) -> m a
run (M m) prog = liftAff do prog m

runEffect :: forall a m. MonadEffect m => Mutex -> (MutexState -> Effect a) -> m a
runEffect (M m) prog = liftEffect do prog m

lock :: forall m. MonadAff m => Mutex -> m Unit
lock self = run self $ 
  \mutex -> Mutex.lock mutex Nothing

lock' :: forall m. MonadAff m => Mutex -> String -> m Unit
lock' self name = run self $ 
  \mutex -> Mutex.lock mutex (Just name)

unlock :: forall m. MonadEffect m => Mutex -> m Unit
unlock self = runEffect self $ 
  \mutex -> Mutex.unlock mutex Nothing

unlock' :: forall m. MonadEffect m => Mutex -> String -> m Unit
unlock' self name = runEffect self $ 
  \mutex -> Mutex.unlock mutex (Just name)

locking :: forall m a. MonadAff m => Mutex -> Aff a -> m a
locking self prog = run self $ 
  \mutex -> Mutex.locking mutex Nothing prog

locking' :: forall m a. MonadAff m => Mutex -> String -> Aff a -> m a
locking' self name prog = run self $ 
  \mutex -> Mutex.locking mutex (Just name) prog
  
isLocked :: forall m. MonadEffect m => Mutex -> m Boolean
isLocked self = runEffect self $ 
  \mutex -> Mutex.isLocked mutex

isLockedBy :: forall m. MonadEffect m => Mutex -> String -> m Boolean
isLockedBy self name = runEffect self $ 
  \mutex -> Mutex.isLockedBy mutex name