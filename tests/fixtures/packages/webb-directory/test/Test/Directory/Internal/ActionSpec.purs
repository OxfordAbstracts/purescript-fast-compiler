module Test.Directory.Internal.ActionSpec where

import Test.Prelude

import Effect.Aff (finally)
import Test.Spec (around_)
import Webb.Directory.Data.Absolute as Abs
import Webb.Directory.Internal.Action as Action
import Webb.Directory.Visitor (newVisitor)
import Webb.Directory.Visitor as Visitor


spec :: Spec Unit
spec = describe "Test internal directory actions" do 
  around_ resetTestDir do 
    run "can detect existing dir" do
      Action.existsDir testDir ?= true
    
    run "cannot detect fake dir" do
      Action.existsDir fakeDir ?= false
      
    run "can create dir" do
      let p = path "apple"
      Action.mkDir p
      Action.existsDir p ?= true
      
    run "can remove dir" do
      let p = path "apple"
      Action.mkDir p
      Action.removeDir p
      Action.existsDir p ?= false
      
    run "can remove all children in a dir" do
      Action.mkDir (path "apple")
      Action.mkDir (path "banana")
      sizeIs testDir 2
      Action.removeDirChildren testDir
      existsDir testDir true
      sizeIs testDir 0

  where
  sizeIs p expected = do
    visitor <- newVisitor p
    size <- Visitor.childCount visitor
    size === expected
    
  existsDir p expected = do
    Action.existsDir p ?= expected

  run msg prog = do 
    it msg do
      Action.eval {} do 
        prog
        pure unit

  fakeDir = Abs.new [] "wallaby-way"
  testDir = Abs.new [] "test-dirs"
  path string = Abs.new ["test-dirs"] string
  
  resetTestDir runTest = do
    let reset = Action.eval {} $ Action.resetDir testDir
    reset 
    finally reset 
      runTest