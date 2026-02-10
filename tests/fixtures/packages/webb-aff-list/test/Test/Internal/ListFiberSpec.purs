module Test.Internal.ListFiberSpec where

import Test.Prelude

import Test.Internal.ListFiber as Props
import Test.Spec (before_)
import Webb.AffList.Internal.ListFiber as LFiber
import Webb.Array as Array
import Webb.Channel as CMaybe
import Webb.Monad.Prelude (delayInt, launch_)
import Webb.Stateful (localEffect)

spec :: Spec Unit
spec = describe "List fiber public API test" do 
  before_ reset do 
    it "can receive value" do 
      f <- new [1, 2, 3, 4]
      receive f
      delayInt 5
      receivedIs [1]
      
    it "can iterate through all values" do 
      f <- new [1, 2, 3, 4]
      forEachReceive f 
      delayInt 5
      receivedIs [1, 2, 3, 4]
      
    it "can conditionally iterate through some values" do 
      f <- new [1, 2, 3, 4]
      whileReceive f
      delayInt 5
      receivedIs [1, 2]
    
  where
  received = localEffect do newShowRef []
  receivedIs n = do
    i <- aread received
    i === n
  reset = (received := [])

  new = Props.new
  
  receive fiber = do 
    launch_ do 
      pvalue <- LFiber.receive fiber
      case pvalue of 
        CMaybe.Closed -> do
          pure unit
        CMaybe.Open val -> do 
          (_ <> [val]) :> received
          
  forEachReceive fiber = do 
    launch_ do
      LFiber.forEach_ fiber \x -> do 
        (_ <> [x]) :> received


  whileReceive fiber = do 
    launch_ do 
      let lessThan n = do 
            arr <- aread received
            pure $ Array.length arr < n

      LFiber.while_ fiber (lessThan 2) \x -> do 
        (_ <> [x]) :> received