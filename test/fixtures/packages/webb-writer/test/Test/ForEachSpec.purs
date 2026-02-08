module Test.ForEachSpec where

import Test.Prelude

import Webb.Writer.ForEach (forEach, each, before, after, inBetween)

spec :: Spec Unit
spec = describe "ForEach tests" do
  describe "using `each`" do
    it "each with many" do 
      let arr = [ 1, 2, 3]
      arr2 <- forEach arr do
        each \a -> pure $ a + 1
      arr2 === [2, 3, 4]

    it "each with 0" do 
      let arr = []
      arr2 <- forEach arr do
        each \a -> pure $ a + 1
      arr2 === []

    it "each with 1" do 
      let arr = [1]
      arr2 <- forEach arr do
        each \a -> pure $ a + 1
      arr2 === [2]
    
    it "no each at all" do
      let arr = [1, 2, 3]
      arr2 :: Array Int <- forEach arr do pure unit
      arr2 === []
      
  it "using before" do
    let arr = [ 1, 2]
    ref <- newShowRef []
    arr2 <- forEach arr do
      before \a -> do
        addLast ref (a * 10)
      each \a -> do 
        addLast ref a
        pure $ a + 1
    aread ref ?= [10, 1, 20, 2]
    arr2 === [2, 3]
    
  it "using after" do
    let arr = [ 1, 2]
    ref <- newShowRef []
    arr2 <- forEach arr do
      after \a -> do
        addLast ref (a * 10)
      each \a -> do 
        addLast ref a
        pure $ a + 1
    aread ref ?= [1, 10, 2, 20]
    arr2 === [2, 3]

  it "using between with many" do
    let arr = [ 1, 2, 3]
    ref <- newShowRef []
    arr2 <- forEach arr do
      inBetween \a -> do
        addLast ref (a * 10)
      each \a -> do 
        addLast ref a
        pure $ a + 1
    aread ref ?= [1, 10, 2, 20, 3]
    arr2 === [2, 3, 4]

  it "using between with 0" do
    let arr = [ ]
    ref <- newShowRef []
    arr2 <- forEach arr do
      inBetween \a -> do
        addLast ref (a * 10)
      each \a -> do 
        addLast ref a
        pure $ a + 1
    aread ref ?= []
    arr2 === []

  it "using between with 1" do
    let arr = [ 1 ]
    ref <- newShowRef []
    arr2 <- forEach arr do
      inBetween \a -> do
        addLast ref (a * 10)
      each \a -> do 
        addLast ref a
        pure $ a + 1
    aread ref ?= [ 1 ]
    arr2 === [2]

  it "using between with 2" do
    let arr = [ 1, 2 ]
    ref <- newShowRef []
    arr2 <- forEach arr do
      inBetween \a -> do
        addLast ref (a * 10)
      each \a -> do 
        addLast ref a
        pure $ a + 1
    aread ref ?= [ 1, 10, 2 ]
    arr2 === [2, 3]
  
  where
  addLast ref a = (_ <> [a]) :> ref

