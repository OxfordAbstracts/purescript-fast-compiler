module Test.Internal.MutexSpec where

import Test.Prelude

import Control.Monad.Error.Class (try)
import Data.Either (isLeft)
import Data.Maybe (Maybe(..))
import Effect.Class (liftEffect)
import Webb.Mutex.Internal.Mutex as Mutex
import Webb.Mutex.Internal.Mutex.State as State
import Webb.Monad.Prelude (delayInt, launch_, throwString)


spec :: Spec Unit
spec = describe "Mutex functions" do
  it "locking competes among mutexes" do 
    i <- newShowRef 0
    mutex <- newMutex
    lock mutex
    launchInc mutex i 
    launchInc mutex i
    
    delayInt 5
    aread i ?= 0
    
    unlock mutex 
    delayInt 5
    aread i ?= 1

    unlock mutex 
    delayInt 5
    aread i ?= 2
    
  it "locking will ensure unlock occurs on error" do
    mutex <- newMutex
    e <- try $ locking mutex do 
      isLocked mutex true
      throwString "hello"
      
    isLeft e === true
    isLocked mutex false
    
  where
  isLocked mutex flag = do
    Mutex.isLocked mutex ?= flag

  locking mutex prog = Mutex.locking mutex Nothing prog

  newMutex = do 
    State.newMutexState # liftEffect
    
  launchInc mutex i = do
    launch_ do
      lock mutex
      (_ + 1) :> i

  lock mutex = do
    Mutex.lock mutex Nothing

  unlock mutex = do
    Mutex.unlock mutex Nothing