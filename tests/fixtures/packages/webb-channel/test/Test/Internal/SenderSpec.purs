module Test.Internal.SenderSpec where

import Test.Prelude

import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)
import Test.Internal.Utils (ritem, unvoidInt)
import Test.Internal.Utils as Utils
import Webb.Channel.Data.ReceiveItem as RItem
import Webb.Channel.Data.ReceiveQueue as RQueue
import Webb.Channel.Data.SendQueue as SQueue
import Webb.Channel.Internal.Sender as Sender
import Webb.Channel.Internal.State as State
import Webb.Monad.Prelude (delayInt, launch_)
import Webb.Result as Result


spec :: Spec Unit
spec = describe "Sender internals" do
  it "sending to no receiver" do
    s <- new
    success <- send s 1
    success === false
    
  it "sending to a receiver" do
    s <- new
    ritem <- addReceiver s
    success <- send s 10
    success === true
    received ritem 10
    
  it "try to send to empty buffer" do
    s <- new' 2
    success <- tryBuffer s 10
    success === true
    bufferIs s [10]
    sendersIs s [10]
    
  it "try to send to full buffer" do
    s <- new' 0
    success <- tryBuffer s 10
    success === false
    bufferIs s []
    sendersIs s []
    
  it "wait with a sender" do 
    ref <- newShowRef 0
    s <- new' 1
    wait s 1 ref
    wait s 2 ref
    bufferIs s [1]
    sendersIs s [1, 2]
    delayInt 20
    aread ref ?= 0 -- Really did wait.
    
  where
  wait s i ref = do
    launch_ do 
      void $ Sender.wait s i
      (_ + 1) :> ref

  bufferIs s ints = do
    this <- Sender.getThis s
    Utils.bufferIs this ints
    
  sendersIs s ints = do
    this <- Sender.getThis s
    Utils.sendersIs this ints

  tryBuffer s i = do
    Sender.tryBuffer s i

  received :: RItem.RItem -> Int -> Aff Unit
  received item i = do 
    let result = RItem.result item
    value <- Result.await result
    unvoidInt <$> value === Just i

  addReceiver s = do 
    state <- Sender.getThis s
    item <- ritem 1
    RQueue.addLast item :> state.receivers
    pure item

  new = do
    state <- State.newState (SQueue.Finite 0)
    sender <- Sender.new state
    pure sender

  new' i = do
    state <- State.newState (SQueue.Finite i)
    sender <- Sender.new state
    pure sender
    
  send s i = do
    Sender.send s i
    