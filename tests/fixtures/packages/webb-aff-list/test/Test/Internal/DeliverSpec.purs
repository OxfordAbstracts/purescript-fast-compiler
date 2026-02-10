module Test.Internal.DeliverSpec where

import Test.Prelude

import Test.Internal.Deliver as DProps
import Test.Spec (before_)
import Webb.AffList.Internal.Deliver as Deliver
import Webb.Channel as CMaybe
import Webb.Monad.Prelude (delayInt, launch_, throwString)
import Webb.Stateful (localEffect)


spec :: Spec Unit
spec = describe "Deliver internals" do 
  before_ reset do
    it "delivers and pauses" do 
      d <- new
      send d 1
      a <- receive d
      a === 1
      
      delayInt 10
      counterIs 0
      

    it "resumes following the second receive" do   
      d <- new
      send d 1
      _ <- receive d
      launch_ $ void (receive d) 
      
      delayInt 10
      counterIs 1
      
    it "doesn't get stuck when receive is first" do 
      d <- new 
      launch_ do 
        void $ receive d
        void $ receive d
      send d 1

      delayInt 10
      counterIs 1

      
    it "closes both channels" do 
      d <- new
      isOpen d true
      
      close d 
      isOpen d false
    
  where 
  counter = localEffect $ newShowRef 0
  reset = (counter := 0)

  new = Deliver.newDeliver
  isOpen = DProps.isOpen
  close = Deliver.close
  
  counterIs n = do
    aread counter ?= n
  
  send d v = do 
    launch_ do 
      void $ Deliver.send d v
      (_ + 1) :> counter

  receive d = do 
    ma <- Deliver.receive d
    case ma of 
      CMaybe.Closed -> 
        throwString "Was closed"
      CMaybe.Open val -> 
        pure val
    



