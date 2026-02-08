module Test.Internal.Mutex.LockerSpec where

import Test.Prelude

import Data.Maybe (Maybe(..))
import Effect.Class (liftEffect)
import Test.Spec.Assertions (expectError)
import Webb.Mutex.Data.Mutex.Id as Id
import Webb.Mutex.Internal.Mutex.Locker as Locker
import Webb.Mutex.Internal.Mutex.State (newMutexState)
import Webb.Mutex.Internal.Mutex.State as State

spec :: Spec Unit
spec = describe "locker" do
  it "initial and unlocked" do
    locker <- newLocker
    
    isLocked locker false
    isLockedById locker 3 false
    sizeIs locker 0
    
  it "lock the unlocked" do
    locker <- newLocker
    success <- Locker.lock locker (Just "bob")
    success === true
    isLocked locker true 
    isLockedById locker 0 false
    isLockedByName locker "bob" true
    sizeIs locker 0

  it "lock the locked fails" do
    locker <- newLocker
    _ <- Locker.lock locker (Just "bob")
    success <- Locker.lock locker (Just "charlie")
    success === false
    isLocked locker true 
    isLockedById locker 0 false
    isLockedByName locker "bob" true
    sizeIs locker 0
    
  it "locking the same name errs" do 
    locker <- newLocker
    _ <- Locker.lock locker (Just "bob")
    expectError do
      Locker.lock locker (Just "bob")
    
  where 
  newLocker = do
    state <- newMutexState # liftEffect
    let locker = Locker.newLocker state
    pure locker
    
  isLocked locker flag = do
    Locker.isLocked locker ?= flag

  isLockedById locker i flag = do
    let id = Id.fromInt i
    Locker.isLockedById locker id ?= flag
    
  isLockedByName locker s flag = do
    Locker.isLockedByName locker s ?= flag
    
  sizeIs locker n = do
    this <- Locker.getThis locker
    State.size this ?= n
