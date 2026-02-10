module Test.Data.ThreadSpec where

import Test.Prelude

import Webb.Monad.Prelude (launch)
import Webb.Thread.Data.Thread as Thread


spec :: Spec Unit
spec = describe "Thread data" do
  it "going to running from starting" do 
    fiber <- launch (pure unit)
    let state = Thread.Starting
    Thread.running fiber state === Thread.Running fiber

  it "going to running from stopped" do
    fiber <- launch (pure unit)
    let state = Thread.Stopped
    Thread.running fiber state === Thread.Stopped