module Webb.Mutex.Internal.Mutex.State where

import Prelude
import Webb.State.Prelude

import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (class MonadEffect)
import Webb.Mutex.Data.Mutex.Id (Id)
import Webb.Mutex.Data.Mutex.Id as Id
import Webb.Mutex.Data.Mutex.Lease (Lease)
import Webb.Mutex.Data.Mutex.Lease as Lease
import Webb.Mutex.Data.Mutex.Queue (Queue)
import Webb.Mutex.Data.Mutex.Queue as Queue


{- The basic shared state of a mutex. -}


type MutexState = 
  { lease :: ShowRef Lease
  , id :: ShowRef Id
  , queue :: ShowRef Queue
  }
  
newMutexState :: Effect MutexState
newMutexState = do
  lease <- newShowRef Lease.none
  id <- newShowRef Id.initial
  queue <- newShowRef Queue.empty
  pure { lease, id, queue }
  
size :: MutexState -> Aff Int
size s = Queue.size <: s.queue

isLocked :: forall m. MonadEffect m => MutexState -> m Boolean
isLocked this = do 
  Lease.isOwned <: this.lease

isLockedByName :: forall m. MonadEffect m => MutexState -> String -> m Boolean
isLockedByName this name = do 
  Lease.isOwnedBy name <: this.lease

isLockedById :: forall m. MonadEffect m => MutexState -> Id -> m Boolean
isLockedById this id = do 
  Lease.hasId id <: this.lease