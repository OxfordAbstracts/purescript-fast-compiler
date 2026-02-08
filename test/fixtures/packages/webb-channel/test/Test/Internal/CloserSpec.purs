module Test.Internal.CloserSpec where

import Test.Prelude

import Test.Internal.Utils as Utils
import Webb.Channel.Data.ReceiveItem as RItem
import Webb.Channel.Data.ReceiveQueue as RQueue
import Webb.Channel.Data.SendItem as SItem
import Webb.Channel.Data.SendQueue as SQueue
import Webb.Channel.Internal.Closer as Closer
import Webb.Channel.Internal.State as State
import Webb.Monad.Prelude (delayInt, launch_, timesRepeat)
import Webb.Result as Result


spec :: Spec Unit
spec = describe "Closer internals" do 
  it "close finishes all pending senders" do 
    ref <- newShowRef 0
    c <- new 3 -- buffer contains 3. So only 7 will get finished.
    addSenders c ref
    sendCountIs c 10
    delayInt 5
    aread ref ?= 0

    close c
    delayInt 10
    aread ref ?= 7

  it "close finishes all receivers" do
    ref <- newShowRef 0
    c <- new 3
    addReceivers c ref
    receiveCountIs c 10
    delayInt 5
    aread ref ?= 0

    close c
    delayInt 5
    aread ref ?= 10 -- all receivers get cancelled
    
  where
  receiveCountIs c n = do
    this <- Closer.getThis c
    Utils.receiveCountIs this n

  sendCountIs c n = do
    this <- Closer.getThis c
    Utils.sendCountIs this n

  close c = do
    Closer.close c
    
  addReceivers c ref = do 
    this <- Closer.getThis c
    items <- timesRepeat 10 do
      item <- Utils.ritem 1
      launch_ do
        void $ Result.await (RItem.result item)
        (_ + 1) :> ref
      pure item
    RQueue.swap items :> this.receivers

  addSenders c ref = do
    this <- Closer.getThis c
    items <- timesRepeat 10 do
      item <- Utils.sitem 1
      launch_ do 
        void $ Result.await (SItem.result item) 
        (_ + 1) :> ref
      pure item
    SQueue.swap items :> this.senders

  new i = do
    state <- State.newState (SQueue.Finite i)
    Closer.new state

