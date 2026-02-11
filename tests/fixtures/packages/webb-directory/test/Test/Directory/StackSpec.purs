module Test.Directory.StackSpec where

import Test.Prelude

import Data.Maybe (Maybe(..))
import Webb.Directory.Data.Absolute as Abs
import Webb.Directory.Data.Stack as Stack


spec :: Spec Unit
spec = describe "Stack state tests" do
  it "is empty" do
    let s = Stack.emptyStack
    sizeEquals s 0
    isEmpty s
    
  it "push" do
    let s = Stack.emptyStack # Stack.push (path "a")
    sizeEquals s 1
    topEquals s "a"
    
  it "push 2" do
    let s = Stack.emptyStack # Stack.push (path "a") >>> Stack.push (path "b")
    sizeEquals s 2
    topEquals s "b"

  it "pop" do
    let 
      s = Stack.emptyStack # 
        Stack.push (path "a") >>> Stack.push (path "b") >>> Stack.pop

    sizeEquals s 1
    topEquals s "a"
    
  it "pop to first" do
    let 
      s = Stack.emptyStack # 
        Stack.push (path "a") >>> Stack.push (path "b") >>> 
        Stack.push (path "c") >>> Stack.popToFirst

    sizeEquals s 1
    topEquals s "a"
    
  it "replace" do
    let s = Stack.emptyStack # Stack.push (path "a") >>> Stack.replace (path "b")
    sizeEquals s 1
    topEquals s "b"
    
  it "view all paths" do
    let s = Stack.emptyStack # Stack.push (path "a") >>> Stack.push (path "b")
        paths = Stack.paths s
    pathsEqual paths ["a", "b"]
    
  it "contains paths" do
    let s = Stack.emptyStack # Stack.push (path "a") >>> Stack.push (path "b")
    Stack.contains (path "a") s === true
    Stack.contains (path "b") s === true
    Stack.contains (path "c") s === false

  where
  path s = Abs.newAbs [] s
  
  sizeEquals stack n = do
    Stack.size stack === n
    
  topEquals stack base = do
    let mtop = Stack.peek stack
        mbase = Abs.basename <$> mtop
    mbase === Just base
    
  isEmpty stack = do
    Stack.isEmpty stack === true
    
  pathsEqual paths strings = do
    let paths' = Abs.basename <$> paths
    paths' === strings

