module Test.ResultSpec where

import Test.Prelude

import Webb.Monad.Prelude (delayInt, launch_)
import Webb.Mutex.Internal.Result as Result


spec :: Spec Unit
spec = describe "Result" do 
  it "can yield via a result" do 
    ref <- newShowRef []
    launch_ do 
      delayInt 0
      (_ <> [1]) :> ref
    launch_ do 
      Result.yield
      (_ <> [2]) :> ref
      
    delayInt 10
    aread ref ?= [2, 1] -- yielding is faster than delay
      

