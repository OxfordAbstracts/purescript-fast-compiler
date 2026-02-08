module Webb.Mutex.Internal.Mutex.Turn where

import Prelude
import Webb.State.Prelude

import Data.Maybe (Maybe)
import Data.Newtype (class Newtype, unwrap, wrap)
import Effect.Aff (Aff)
import Webb.Mutex.Data.Mutex.Id (Id)
import Webb.Mutex.Data.Mutex.Id as Id
import Webb.Mutex.Data.Mutex.Item as Item
import Webb.Mutex.Data.Mutex.Lease as Lease
import Webb.Mutex.Data.Mutex.Queue as Queue
import Webb.Mutex.Internal.Mutex.State (MutexState)
import Webb.Mutex.Internal.Mutex.Unlocker as Unlocker
import Webb.Result as Result
import Webb.Monad.Prelude (onCancel)


{- Represents the concept of waiting your turn for the mutex. -}


newtype Turn = T MutexState

derive instance Newtype Turn _

newTurn :: MutexState -> Turn
newTurn = wrap

getThis :: Turn -> Aff MutexState
getThis = unwrap >>> pure

-- Wait our turn to be dequeued.
wait :: Turn -> Maybe String -> Aff Unit
wait t mname = do
  this <- getThis t
  result <- newResult
  id <- nextId
  let item = Item.newItem id mname result
  Queue.enqueue item :> this.queue
  
  -- We have to await the result, but it's possible that we could be cancelled
  -- at this stage (no error should occur). For that reason, we prepare for a reseet
  -- on cancellation.
  onCancel (reset t id) do
    Result.await result
  
  where
  newResult = do 
    Result.newResult

  nextId = do
    -- We use the current id before bumping to the next one.
    this <- getThis t
    id <- aread this.id
    Id.next :> this.id
    pure id
  
-- If an error occurs, reset the state back to what it needs to be.
reset :: Turn -> Id -> Aff Unit
reset t id = do
  ifM isOwner (do
    let unlocker = Unlocker.newUnlocker (unwrap t)
    Unlocker.giveToNextOwner unlocker
  ) (do 
    removeFromQueue  
  )
  where
  isOwner = do 
    this <- getThis t
    Lease.hasId id <: this.lease
    
  removeFromQueue = do
    this <- getThis t
    Queue.removeId id :> this.queue

  
  