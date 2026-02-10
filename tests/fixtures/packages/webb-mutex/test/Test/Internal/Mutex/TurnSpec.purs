module Test.Internal.Mutex.TurnSpec where

import Test.Prelude

import Data.Maybe (Maybe(..))
import Effect.Class (liftEffect)
import Webb.Mutex.Data.Mutex.Id as Id
import Webb.Mutex.Data.Mutex.Item as Item
import Webb.Mutex.Data.Mutex.Lease as Lease
import Webb.Mutex.Data.Mutex.Queue as Queue
import Webb.Mutex.Internal.Mutex.State as State
import Webb.Mutex.Internal.Mutex.Turn as Turn
import Webb.Mutex.Internal.Mutex.Unlocker as Unlocker
import Webb.Result as Result
import Webb.Monad.Prelude (_kill, delayInt, launch)

spec :: Spec Unit
spec = describe "Turn abstraction allows waiting" do

  it "waiting is finished by unlocking" do 
    turn <- newTurn
    i <- newShowRef 0
    _ <- launchInc turn i
    
    delayInt 4
    aread i ?= 0

    unlock turn
    delayInt 4
    aread i ?= 1
    
  it "cancellation when you own it will dequeue the next item" do
    turn <- newTurn
    i <- newShowRef 0
    fiber <- launchInc turn i
    
    setOwner turn 0 -- same owner as the thread.
    clearQueue turn -- Clear the waiter from the queue.
    enqueue turn 2
    isLocked turn true 
    isLockedBy turn 0 true
    
    _kill fiber
    delayInt 5
    isLocked turn true 
    isLockedBy turn 2 true
    
  it "cancellation when you _don't_ own it will remove the item from the queue" do
    turn <- newTurn
    i <- newShowRef 0
    fiber <- launchInc turn i
    
    sizeIs turn 1
    
    _kill fiber
    delayInt 5
    sizeIs turn 0
    isLocked turn false 
    
  where
  sizeIs turn i = do
    this <- Turn.getThis turn
    State.size this ?= i

  clearQueue turn = do 
    state <- Turn.getThis turn
    state.queue := Queue.empty

  isLocked turn flag = do
    state <- Turn.getThis turn
    State.isLocked state ?= flag

  isLockedBy turn i flag = do
    let id = Id.fromInt i
    state <- Turn.getThis turn
    State.isLockedById state id ?= flag

  setOwner turn i = do
    let id = Id.fromInt i
    state <- Turn.getThis turn
    state.lease := Lease.newLease id Nothing
    
  enqueue turn i = do
    this <- Turn.getThis turn
    let id = Id.fromInt i
    result <- Result.newResult
    let item = Item.newItem id Nothing result
    Queue.enqueue item :> this.queue

  unlock turn = do
    state <- Turn.getThis turn
    unlocker <- pure $ Unlocker.newUnlocker state
    Unlocker.giveToNextOwner unlocker

  newTurn = do 
    state <- State.newMutexState # liftEffect
    pure $ Turn.newTurn state
    
  launchInc turn i = do
    launch do
      Turn.wait turn Nothing
      (_ + 1) :> i
