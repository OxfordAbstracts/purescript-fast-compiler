module Test.Internal.ChannelSpec where

import Test.Prelude

import Data.Foldable as Fold
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)
import Test.Internal.Utils as Utils
import Webb.Channel as Chane
import Webb.Channel.Data.SendQueue as SQueue
import Webb.Channel.Internal.Channel as Chan
import Webb.Channel.Internal.State as State
import Webb.Monad.Prelude (delayInt, launch_, traceM)


spec :: Spec Unit
spec = describe "Channel internals" do
  it "can receive from sender" do
    ref <- newRef
    chan <- new 0
    send chan ref 10
    receive chan ref
    
    delayInt 5
    aread ref ?= [10]
    
  it "can send to receiver" do
    ref <- newRef
    chan <- new 0
    receive chan ref
    send chan ref 10
    
    delayInt 5
    aread ref ?= [10]
    
  it "send multiple, then receive" do 
    ref <- newRef
    chan <- new 0
    send chan ref 1
    send chan ref 2
    send chan ref 3
    receive chan ref
    receive chan ref
    receive chan ref
    
    delayInt 5
    aread ref ?= [1, 2, 3]

  it "receive multiple, then send" do 
    ref <- newRef
    chan <- new 0
    receive chan ref
    receive chan ref
    receive chan ref
    send chan ref 1
    send chan ref 2
    send chan ref 3
    
    delayInt 5
    aread ref ?= [1, 2, 3]

  it "interleave sends and receives" do
    ref <- newRef
    chan <- new 0
    send chan ref 1
    receive chan ref
    receive chan ref
    send chan ref 2
    send chan ref 3
    receive chan ref
    
    -- The 3 gets deferred longer than the 2 because of the
    -- nature of Aff. Attempts to fix this with a delayInt did not
    -- work, unfortunately.
    delayInt 5
    aread ref ?= [1, 3, 2]
    
  it "receives are made in order" do
    ref <- newRef
    chan <- new 0
    send chan ref 1
    send chan ref 2
    receive' chan ref 11
    receive' chan ref 12
    delayInt 5
    aread ref ?= [11, 12]
    
  it "when closed, sending and receiving do not work" do 
    ref <- newRef
    chan <- new 0
    close chan
    send chan ref 1
    send chan ref 2
    receive' chan ref 11
    receive' chan ref 12
    delayInt 5
    aread ref ?= []
    
  it "closing will flush allow buffered sends to be received" do 
    ref <- newRef
    chan <- new 2
    send chan ref 1
    send chan ref 2
    send chan ref 3 -- This one did not make it into the buffer
    close chan
    receive chan ref
    receive chan ref
    receive chan ref
    
    delayInt 10
    aread ref ?= [1, 2]
  
  it "trying to send can fail" do 
    chan <- new 0
    success <- Chan.trySend chan 2
    success === false
    
  it "trying to receive can fail" do 
    chan <- new 0
    mvalue :: Maybe Int <- Chan.tryReceive chan
    mvalue === Nothing
    
  it "open and close is tracked" do 
    chan <- new 0
    Chan.isOpen chan ?= true
    Chan.isClosed chan ?= false
    
    Chan.close chan
    Chan.isOpen chan ?= false
    Chan.isClosed chan ?= true
    
  where
  {-}
  print :: Chan.Channel -> Aff Unit
  print c = do
    str <- toString c
    traceM str
  -}
    
  close chan = do 
    Chan.close chan

  newRef = do newShowRef ([] :: Array Int)
  
  new i = do
    state <- State.newState (SQueue.Finite i)
    pure state
    
  send chan _ref i = do
    launch_ do
      void $ Chan.send chan i
      
  receive chan ref = do
    launch_ do 
      mval <- Chan.receive chan
      Fold.for_ mval \val -> do
        (_ <> [val]) :> ref

  receive' chan ref i = do
    launch_ do 
      mval <- Chan.receive chan
      Fold.for_ mval \_ -> do
        (_ <> [i]) :> ref


toString :: Chan.Channel -> Aff String
toString c = do
  senders <- Utils.senders c
  pure $ show
    { id: c.id
    , open: c.open
    , receivers: c.receivers
    , senders: senders
    }
