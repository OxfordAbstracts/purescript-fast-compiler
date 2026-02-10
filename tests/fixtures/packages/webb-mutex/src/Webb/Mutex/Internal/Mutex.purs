module Webb.Mutex.Internal.Mutex where

import Prelude
import Webb.State.Prelude

import Data.Maybe (Maybe)
import Effect.Aff (Aff, finally)
import Effect.Class (class MonadEffect)
import Webb.Mutex.Internal.Mutex.Locker as Locker
import Webb.Mutex.Internal.Mutex.State (MutexState)
import Webb.Mutex.Internal.Mutex.State as State
import Webb.Mutex.Internal.Mutex.Turn as Turn
import Webb.Mutex.Internal.Mutex.Unlocker as Unlocker

type Mutex = MutexState

{- Implement the important mutex functions for the whole mutex. -}

-- Lock. Implemented in a model-based method, to summon the desired thoughts
-- while reading it.
lock :: Mutex -> Maybe String -> Aff Unit
lock mutex mname = do
  locker <- newLocker
  success <- Locker.lock locker mname
  unless success do 
    turn <- newTurn
    Turn.wait turn mname
    
  where
  newLocker = do pure $ Locker.newLocker mutex
  newTurn = do pure $ Turn.newTurn mutex
  
-- Unlock with the given name.
unlock :: forall m. MonadEffect m => Mutex -> Maybe String -> m Unit
unlock mutex mname = do 
  unlocker <- newUnlocker 
  Unlocker.unlock unlocker mname
  where
  newUnlocker = do pure $ Unlocker.newUnlocker mutex
  
locking :: forall a. Mutex -> Maybe String -> Aff a -> Aff a
locking mutex mname prog = do 
  lock mutex mname
  finally (unlock mutex mname) do
    prog
    
isLocked :: forall m. MonadEffect m => Mutex -> m Boolean
isLocked mutex = do State.isLocked mutex

isLockedBy :: forall m. MonadEffect m => Mutex -> String -> m Boolean
isLockedBy mutex name = do State.isLockedByName mutex name

