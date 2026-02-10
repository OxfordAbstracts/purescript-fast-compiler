module Test.Internal.StateSpec where

import Test.Prelude

import Data.Traversable (sequence)
import Effect.Aff (Aff)
import Webb.Channel.Data.Id as Id
import Webb.Channel.Data.ReceiveItem as RItem
import Webb.Channel.Data.ReceiveQueue as RQueue
import Webb.Channel.Data.SendItem as SItem
import Webb.Channel.Data.SendQueue as SQueue
import Webb.Channel.Internal.State (CState)
import Webb.Channel.Internal.State as State
import Webb.Result as Result



spec :: Spec Unit
spec = describe "State internals" do
  it "initial" do 
    s <- state [] []
    isOpen s true
    idIs s 0
    sendCount s 0
    receiveCount s 0
    
  it "next id" do 
    s <- state [] []
    current <- State.nextId s
    current === Id.fromInt 0
    idIs s 1
    
  it "not empty" do 
    s <- state [1, 2, 3] [2, 4]
    sendCount s 3
    receiveCount s 2
    
  it "close" do 
    s <- state [] []
    State.close s
    isOpen s false
    
  where 
  isOpen s flag = do 
    State.isOpen s ?= flag
    
  idIs s n = do
    aread s.id ?= Id.fromInt n
    
  sendCount s n = do
    State.sendSize s ?= n

  receiveCount s n = do
    State.receiveSize s ?= n
  
  state :: Array Int -> Array Int -> Aff CState
  state sints rints = do
    sitems <- sequence (sitem <$> sints)
    ritems <- sequence (ritem <$> rints)
    s <- State.newState (SQueue.Finite 0)
    SQueue.swap sitems :> s.senders
    RQueue.swap ritems :> s.receivers
    pure s
    
  sitem :: Int -> Aff SItem.SItem
  sitem i = do
    result <- Result.newResult
    let id = Id.fromInt i
    let value = i
    pure $ SItem.newItem value id result
    
  ritem :: Int -> Aff RItem.RItem
  ritem i = do 
    result <- Result.newResult
    let id = Id.fromInt i
    pure $ RItem.newItem id result
    

