module Test.Internal.Node.PortSpec where

import Test.Prelude

import Effect.Exception (error)
import Test.Internal.Node.Port as Props
import Test.Spec (before_)
import Webb.AffList.Data.Node.Port as PortValue
import Webb.AffList.Internal.Node.Port as Port
import Webb.Monad.Prelude (delayInt, launch_)
import Webb.Stateful (localEffect)


spec :: Spec Unit
spec = describe "Port internals" do 
  before_ reset do
    it "sending starts the program" do 
      p <- new' (\port -> send port 2)
      send p 1
      receive p
      
      delayInt 5
      receivedIs 1
      
      receive p
      delayInt 5
      receivedIs 2 -- this value was caused by the initial send starting the program.
      
    it "receiving will start the program" do 
      p <- new' (\port -> send port 1)
      receive p
      
      delayInt 5
      receivedIs 1 -- We received a 1 because the 'receive' triggered the program.
      
    it "submitting an error does not require a second receive to continue" do 
      p <- new
      receive p
      err p "hello"
      delayInt 5
      receivedIs (-1000)
      
    it "closing works as expected" do 
      p <- new
      isOpen p true
      receive p
      close p
      delayInt 5
      receivedIs (-100)
      isOpen p false
    
  where
  received = localEffect do newShowRef (-1)
  reset = (received := -1)
  receivedIs n = do 
    aread received ?= n

  new = Props.new
  new' = Props.new'
  
  isOpen = Props.isOpen
  
  err p string = do
    void $ Port.error p (error string)
    
  close p = do 
    void $ Port.close p
  
  send port n = do
    launch_ do
      void $ Port.send port n
      
  receive port = do 
    launch_ do 
      mval <- Port.receive port
      val <- case mval of 
        PortValue.Closed -> do 
          pure (-100)
        PortValue.Err _ -> do 
          pure (-1000)
        PortValue.Value v -> do 
          pure v
      received := val
    
