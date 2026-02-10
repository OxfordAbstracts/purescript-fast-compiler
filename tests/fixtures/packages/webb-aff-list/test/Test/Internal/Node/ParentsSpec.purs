module Test.Internal.Node.ParentsSpec where

import Test.Prelude

import Test.Internal.Node.Parents as PProps
import Webb.AffList.Internal.Node.Parents as Parents



spec :: Spec Unit 
spec = describe "Parents internals" do 
  it "empty" do 
    parents <- new []
    parentsAre parents []
    
  it "full" do 
    parents <- new [true, true]
    parentsAre parents [true, true]
    
  it "stop" do 
    parents <- new [true, true]
    stop parents
    parentsAre parents [false, false]
    
  it "add parent" do 
    parents <- new [false, false]
    addNew parents
    parentsAre parents [false, false, true]
    countIs parents 3

  where
  new = PProps.new 
  stop = Parents.stop
  parentsAre = PProps.parentsAre
  addNew ps = do 
    fake <- PProps.newFakeParent
    Parents.addParent ps fake
  countIs = PProps.countIs

