module Test.Directory.AbsoluteSpec where

import Test.Prelude

import Data.Maybe (Maybe(..))
import Effect.Class (liftEffect)
import Node.Process as Process
import Webb.Directory.Data.Absolute as Abs
import Webb.Directory.Data.Absolute ((++))


spec :: Spec Unit
spec = describe "Absolute path tests" do
  it "path resolves when given a directory" do 
    let path = Abs.newAbs [ "/a"] "b"
    pathEquals path "/a/b"
    
  it "if no parent directory is specified, the current working directory is used" do
    let path = Abs.newAbs [] "b"
    cwd <- Process.cwd # liftEffect
    pathEquals path $ cwd <> "/b"
    
  it "can get base name of the path" do
    let path = Abs.new ["/a/b/c"] "d"
    Abs.basename path === "d"
    
  it "can get parent of the path" do
    let path = Abs.new ["/a"] "b"
        mparent = Abs.parent path
    
    Abs.asString <$> mparent === Just "/a"
    
  it "can get the root as a parent" do
    let path = Abs.new [] "/b"
        mparent = Abs.parent path
    
    Abs.asString <$> mparent === Just "/"
    
  it "cannot get parent of the root" do
    let path = Abs.new [] "/"
        mparent = Abs.parent path
    
    Abs.asString <$> mparent === Nothing
    
  it "can extend path" do
    let 
      path = Abs.new [] "/a"
      child = path ++ "b"
    pathEquals child "/a/b" 

  it "can extend upward" do
    let 
      path = Abs.new [] "/a"
      child = path ++ ".."
    pathEquals child "/" 
    
  it "understands depth" do 
    let root = Abs.new [] "/"
        path = Abs.new [] "/a"
        path' = Abs.new [] "/a/"
        child = path ++ "babe"
    depthEquals root 0
    depthEquals path 1
    depthEquals path' 1
    depthEquals child 2

  where
  pathEquals path string = do
    Abs.unwrap path === string
    
  depthEquals path n = do 
    Abs.depth path === n
