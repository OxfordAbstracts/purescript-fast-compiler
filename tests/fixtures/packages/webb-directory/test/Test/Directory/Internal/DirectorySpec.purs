module Test.Directory.Internal.DirectorySpec where

import Test.Prelude

import Effect.Aff (finally)
import Effect.Class (liftEffect)
import Node.Path as Path
import Node.Process as Process
import Test.Spec (around_)
import Test.Spec.Assertions (expectError)
import Webb.Directory.Data.Absolute as Abs
import Webb.Directory.Data.Stack as Stack
import Webb.Directory.Internal.Directory as Dir


spec :: Spec Unit
spec = describe "Test internal directory" do
  around_ restoreCwd do
    run "initializes to current directory" do
      cwd <- Process.cwd # liftEffect  
      topEquals cwd
      sizeEquals 1
      Dir.isFirst ?= true
      
    run "has source directory" do
      Dir.containsDirName "src" ?= true
      
    run "has spago file" do
      Dir.containsFileName "spago.yaml" ?= true
      
    run "can extend name based on own current directory" do 
      name <- Dir.makeName "lol"
      cwd <- Process.cwd # liftEffect
      pathIdentical name $ cwd <> "/lol"
      
    run "can push a REAL directory" do 
      child <- Dir.makeName "src"
      Dir.push child
      topIs child
      sizeEquals 2
      cwdEquals child
      
    run "cannot push a FAKE directory" do
      expectError do
        child <- Dir.makeName "lol"
        Dir.push child

    run "can replace a REAL directory" do 
      child1 <- Dir.makeName "src"
      child2 <- Dir.makeName "test"
      Dir.push child1
      Dir.replace child2
      topIs child2
      sizeEquals 2
      cwdEquals child2

    run "can pop a directory" do 
      cwd <- Dir.makeName ""
      child1 <- Dir.makeName "src"
      Dir.push child1
      Dir.pop
      topIs cwd
      sizeEquals 1
      cwdEquals cwd
      
    run "cannot pop the first directory" do
      cwd <- Dir.makeName ""
      Dir.pop
      topIs cwd
      sizeEquals 1
    
  where 
  topIs path = do
    curr <- Dir.current
    curr === path

  topEquals str = do
    path <- Dir.current
    Abs.basename path === Path.basename str
    
  sizeEquals n = do
    size <- Dir.size 
    n === size

  run msg prog = do 
    it msg do
      stack <- newShowRef Stack.emptyStack
      let env = { stack }
      Dir.eval env do
        Dir.init
        _ <- prog
        pure unit
        
  pathIdentical path string = do
    Abs.unwrap path === string

  cwdEquals absPath = do
    cwd <- Process.cwd # liftEffect
    Abs.unwrap absPath === cwd

  restoreCwd runTest = do
    cwd <- Process.cwd # liftEffect
    finally (do
      Process.chdir cwd # liftEffect
    ) $ do
      runTest
      