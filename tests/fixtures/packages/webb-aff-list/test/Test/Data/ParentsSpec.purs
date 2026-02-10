module Test.Data.ParentsSpec where

import Test.Prelude

import Test.Data.Parents as P


spec :: Spec Unit
spec = describe "Parents data" do 
  it "empty" do 
    let arr = empty
    sizeIs arr 0
    
  it "adding" do 
    let arr = addParent fakeParent empty
    sizeIs arr 1
    
    let arr' = addParent fakeParent arr
    sizeIs arr' 2
  
  where
  -- Many modules may define properties. We import them from multiple, and use them
  -- in the test as if they all came from the same place.
  sizeIs = P.sizeIs
  addParent = P.addParent
  fakeParent = P.fakeParent
  empty = P.empty