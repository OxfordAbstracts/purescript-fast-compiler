module Test.Directory.Internal.VisitorSpec where

import Test.Prelude

import Effect.Aff (finally)
import Effect.Class (liftEffect)
import Node.Path as Path
import Node.Process as Process
import Test.Spec (around_)
import Webb.Directory.Data.Absolute as Abs
import Webb.Directory.Data.Stack as Stack
import Webb.Directory.Internal.Visitor as Vis


spec :: Spec Unit
spec = describe "Test internal directory" do
  around_ restoreCwd do
    run "initializes to current directory" do
      cwd <- Process.cwd # liftEffect  
      topEquals cwd
      sizeEquals 1
      Vis.isFirst ?= true
      
    run "has source directory" do
      Vis.containsDirName "src" ?= true
      
    run "has spago file" do
      Vis.containsFileName "spago.yaml" ?= true
      
    run "can extend name based on own current directory" do 
      name <- Vis.makeName "lol"
      cwd <- Process.cwd # liftEffect
      pathIdentical name $ cwd <> "/lol"
      
    run "can push a REAL directory" do 
      child <- Vis.makeName "src"
      Vis.push child
      topIs child
      sizeEquals 2
      cwdNotEquals child
      
    run "can push a FAKE directory" do
      child <- Vis.makeName "lol"
      Vis.push child

    run "can replace a REAL directory" do 
      child1 <- Vis.makeName "src"
      child2 <- Vis.makeName "test"
      Vis.push child1
      Vis.replace child2
      topIs child2
      sizeEquals 2
      cwdNotEquals child2

    run "can pop a directory" do 
      cwd <- Vis.makeName ""
      child1 <- Vis.makeName "src"
      Vis.push child1
      Vis.pop
      topIs cwd
      sizeEquals 1
      
    run "cannot pop the first directory" do
      cwd <- Vis.makeName ""
      Vis.pop
      topIs cwd
      sizeEquals 1
    
  where 
  topIs path = do
    curr <- Vis.current
    curr === path

  topEquals str = do
    path <- Vis.current
    Abs.basename path === Path.basename str
    
  sizeEquals n = do
    size <- Vis.size 
    n === size

  run msg prog = do 
    it msg do
      stack <- newShowRef Stack.emptyStack
      cwd <- Process.cwd # liftEffect
      let env = { stack }
      Vis.eval env do
        Vis.init (Abs.new [] cwd)
        _ <- prog
        pure unit
        
  pathIdentical path string = do
    Abs.unwrap path === string

  cwdNotEquals absPath = do
    cwd <- Process.cwd # liftEffect
    Abs.unwrap absPath !== cwd

  restoreCwd runTest = do
    cwd <- Process.cwd # liftEffect
    finally (do
      Process.chdir cwd # liftEffect
    ) $ do
      runTest
      