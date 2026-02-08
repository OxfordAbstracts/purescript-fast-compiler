module Test.Internal.NodeSpec where

import Test.Prelude

import Effect.Aff (never)
import Test.Internal.Node as Props
import Webb.AffList.Data.Node.Port as PortValue
import Webb.AffList.Internal.Node as Node
import Webb.Monad.Prelude (delayInt, launch_)
import Webb.Stateful (localEffect)


spec :: Spec Unit
spec = describe "Node public api test" do 
  it "can send and receive a value" do 
    n <- new \node -> send node 2
    receive n  
    delayInt 5
    receivedIs 2
    
  it "when program is done running, it stops" do 
    n <- new \node -> send node 2
    receive n
    delayInt 5
    isStarted n false
    
  it "node can be manually stopped" do 
    n <- new \_node -> never
    receive n

    delayInt 5
    isStarted n true
    
    stop n
    delayInt 5
    isStarted n false
    
  it "parents can be added and stop with the node" do 
    n <- new' [true, true]
    receive n
    
    delayInt 5
    parentsAre n [true, true]
    
    stop n
    delayInt 5
    parentsAre n [false, false]

    
  where
  received = localEffect $ newShowRef (-1)
  receivedIs i = do 
    aread received ?= i
    
  isStarted = Props.isStarted

  new = Props.new
  new' = Props.new'
  parentsAre = Props.parentsAre
  
  send n i = do 
    launch_ do void $ Node.send n i
    
  receive n = do 
    launch_ do 
      pvalue <- Node.receive n
      case pvalue of 
        PortValue.Value val -> received := val
        PortValue.Err _ -> received := -100
        PortValue.Closed -> received := -1000
        
  stop = Node.stop

