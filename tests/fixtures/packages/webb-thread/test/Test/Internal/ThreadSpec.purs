module Test.Internal.ThreadSpec where

import Test.Prelude

import Effect.Aff (invincible, never)
import Webb.Monad.Prelude (delayInt, launch_)
import Webb.Thread.Internal.Thread as Thread

spec :: Spec Unit
spec = describe "Thread internals" do
  it "Starting thread can immediately stop" do 
    thread <- new
    isStopped thread true
    
    Thread.start thread 
    isStopped thread true
    Thread.isStopped thread ?= true

  it "Starting thread can will stay stopped" do 
    thread <- new
    isStopped thread true

    Thread.start thread 
    delayInt 20
    isStopped thread true
    Thread.isStopped thread ?= true
    
  it "Starting thread can modify value" do 
    i <- newShowRef 0
    thread <- new
    Thread.setProgram thread $ (_ + 1) :> i
    
    Thread.start thread
    isStopped thread true
    equals i 1

  it "can stop thread by cancellation" do
    thread <- new
    Thread.setProgram thread never
    
    Thread.start thread
    delayInt 20
    isStopped thread false
    
    Thread.stop thread
    isStopped thread true

  it "cannot stop thread if invincible" do
    thread <- new
    Thread.setProgram thread $ invincible never
    
    Thread.start thread
    delayInt 20
    isStopped thread false
    
    launch_ do
      Thread.stop thread

    delayInt 20
    isStopped thread false -- cannot stop it. The aff was invincible
    
  where
  new = Thread.newThread

  isStopped thread flag = do
    Thread.isStopped thread ?= flag

  equals ref val = do
    aread ref ?= val