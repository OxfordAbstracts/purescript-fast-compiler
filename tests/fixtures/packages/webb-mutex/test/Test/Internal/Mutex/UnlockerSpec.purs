module Test.Internal.Mutex.UnlockerSpec where

import Test.Prelude

import Data.Maybe (Maybe(..))
import Effect.Class (liftEffect)
import Test.Spec.Assertions (expectError)
import Webb.Mutex.Data.Mutex.Id as Id
import Webb.Mutex.Data.Mutex.Item as Item
import Webb.Mutex.Data.Mutex.Lease as Lease
import Webb.Mutex.Data.Mutex.Queue as Queue
import Webb.Mutex.Internal.Mutex.State as State
import Webb.Mutex.Internal.Mutex.Unlocker as Unlocker
import Webb.Result as Result
import Webb.Monad.Prelude (delayInt, forceMaybe', launch_)


spec :: Spec Unit
spec = describe "unlocker functionality" do
  it "empty" do
    u <- newUnlocker
    isLocked u false
    isLockedById u 0 false
    
  it "unlock empty" do
    u <- newUnlocker
    Unlocker.unlock u Nothing
    isLocked u false
    isLockedById u 0 false
    
  it "unlock locked with no queue" do
    u <- newUnlocker

    lock u 2
    isLocked u true
    isLockedById u 2 true
    
    Unlocker.unlock u Nothing
    isLocked u false
    isLockedById u 2 false
    
  it "unlock a locked mutex with a queued item" do
    u <- newUnlocker
    
    lock u 2
    enqueue u 3
    sizeIs u 1 
    
    Unlocker.unlock u Nothing
    isLocked u true
    isLockedById u 3 true
    sizeIs u 0
    
  it "errs if unlocks with name, but isn't owner" do
    u <- newUnlocker
    lock u 2
    expectError do
      Unlocker.unlock u (Just "bob")
      
  it "unlocking to new owner will release the result" do
    u <- newUnlocker
    lock u 2
    enqueue u 3
    i <- newShowRef 0
    launchToIncrement u i
    
    Unlocker.unlock u Nothing
    delayInt 50
    aread i ?= 1
    
  where
  launchToIncrement u i = do
    launch_ do
      this <- Unlocker.getThis u
      mfirst <- Queue.peek <: this.queue
      item <- forceMaybe' "No first item" mfirst
      let result = Item.result item
      Result.await result
      (_ + 1) :> i

  enqueue u i = do 
    let id = Id.fromInt i
    state <- Unlocker.getThis u
    result <- Result.newResult
    let item = Item.newItem id Nothing result
    Queue.enqueue item :> state.queue

  lock u i = do
    let id = Id.fromInt i
    state <- Unlocker.getThis u
    let lease = Lease.newLease id Nothing
    state.lease := lease

  newUnlocker = do 
    state <- State.newMutexState # liftEffect
    pure $ Unlocker.newUnlocker state
    
  sizeIs u n = do 
    this <- Unlocker.getThis u
    State.size this ?= n
    
  isLocked u flag = do 
    this <- Unlocker.getThis u
    State.isLocked this ?= flag
    
  isLockedById u i flag = do
    let id = Id.fromInt i
    this <- Unlocker.getThis u
    State.isLockedById this id ?= flag



