module Webb.Mutex.Internal.Mutex.Unlocker where

import Prelude
import Webb.State.Prelude

import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype, unwrap, wrap)
import Effect.Class (class MonadEffect)
import Webb.Monad.Prelude (expect)
import Webb.Mutex.Data.Mutex.Item (Item)
import Webb.Mutex.Data.Mutex.Item as Item
import Webb.Mutex.Data.Mutex.Lease as Lease
import Webb.Mutex.Data.Mutex.Queue as Queue
import Webb.Mutex.Internal.Mutex.State (MutexState)
import Webb.Mutex.Internal.Result as Result


newtype Unlocker = U MutexState

derive instance Newtype Unlocker _

newUnlocker :: MutexState -> Unlocker
newUnlocker = wrap

getThis :: forall m. MonadEffect m => Unlocker -> m MutexState
getThis = unwrap >>> pure

-- Attempt to unlock with the given name. If it's the _wrong_ name attempting
-- to unlock, then some lock thinks it has the lock when it does not.
-- So we error. Otherwise, we grant to the next item in the queue, if any.
unlock :: forall m. MonadEffect m => Unlocker -> Maybe String -> m Unit
unlock u mname = do
  checkName 
  giveToNextOwner u
  
  where 
  checkName = do
    this <- getThis u
    case mname of
      Nothing -> do 
        -- If no name, then no request for validation.
        pure unit
      Just name -> do 
        correctOwner <- Lease.isOwnedBy name <: this.lease
        currentName <- Lease.name <: this.lease
        expect correctOwner $ 
          "Unlocked by incorrect name '" <> name <> "', but expected '" 
            <> show currentName <> "'"

giveToNextOwner :: forall m. MonadEffect m => Unlocker -> m Unit
giveToNextOwner u = do
  clearLease u
  mitem <- dequeueNextItem u
  for_ mitem \item -> do
    setNewOwner u item
    notifyThread u item

clearLease :: forall m. MonadEffect m => Unlocker -> m Unit
clearLease u = do
  this <- getThis  u
  this.lease := Lease.none
  
dequeueNextItem :: forall m. MonadEffect m => Unlocker -> m (Maybe Item)
dequeueNextItem u = do
  this <- getThis u

  mnext <- Queue.peek <: this.queue 
  Queue.dequeue :> this.queue
  pure mnext
  
setNewOwner :: forall m. MonadEffect m => Unlocker -> Item -> m Unit
setNewOwner u item = do
  this <- getThis u
  let newLease = Lease.fromItem item
  this.lease := newLease
  
notifyThread :: forall m. MonadEffect m => Unlocker -> Item -> m Unit
notifyThread _ item = do
  Result.return (Item.result item) unit