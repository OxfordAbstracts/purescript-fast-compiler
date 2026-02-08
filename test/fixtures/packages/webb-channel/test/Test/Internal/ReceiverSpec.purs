module Test.Internal.ReceiverSpec where

import Test.Prelude

import Data.Maybe (Maybe(..), isNothing)
import Test.Internal.Utils as Utils
import Webb.Channel.Data.SendQueue as SQueue
import Webb.Channel.Internal.Receiver as Receiver
import Webb.Channel.Internal.State as State
import Webb.Monad.Prelude (delayInt, launch_)


spec :: Spec Unit
spec = describe "Receiver internals" do
  it "receiving from no sender" do
    r <- new
    mval <- receive r
    isNothing mval === true
  
  it "receiving from a sender" do 
    r <- new
    send r 1
    mval <- receive r
    mval === Just 1
    
  it "waiting really does wait" do 
    ref <- newShowRef 0
    r <- new
    wait r ref
    receiveCountIs r 1

    delayInt 5
    aread ref ?= 0
  
  where

  wait r ref = do
    launch_ do
      void $ Receiver.wait r
      (_ + 1) :> ref
      
  receiveCountIs r i = do
    this <- Receiver.getThis r
    Utils.receiveCountIs this i

  send r i = do
    this <- Receiver.getThis r
    item <- Utils.sitem i
    SQueue.addLast item :> this.senders

  new = do 
    state <- State.newState (SQueue.Finite 0)
    Receiver.new state
    
  receive r = do
    Receiver.receive r


