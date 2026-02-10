module Test.Internal.Node.ProgramSpec where

import Test.Prelude

import Effect.Aff (never, throwError)
import Test.Internal.Node.Program as Props
import Test.Spec (before_)
import Webb.AffList.Internal.Node.Program as Program
import Webb.Monad.Prelude (delayInt, throwString)



spec :: Spec Unit
spec = describe "Program internals" do 
  before_ (pure unit) do
    describe "basic tests" do 
      it "initially state" do 
        p <- new
        isStarted p false
        isOpen p true
        parentsAreActive p true
        
      it "starting succeeds" do 
        p <- new
        start p
        delayInt 10
        isStarted p true
        isOpen p true
        parentsAreActive p true
        
      it "internal stop succeeds" do 
        p <- new
        start p
        internalStop p
        isStarted p false
        isOpen p false
        parentsAreActive p false
        
      it "external stop succeeds" do 
        p <- new
        start p
        externalStop p
        isStarted p false
        isOpen p false
        parentsAreActive p false
        
    describe "tests with a program" do 
      it "starting will trigger internal stop on its own" do 
        p <- new' do pure unit
        start p
        isStarted p true

        delayInt 10
        isStarted p false
        isOpen p false
        parentsAreActive p false
        
      it "error will trigger internal stop on its own" do
        p <- new' do throwString "oh no, error"
        start p
        isStarted p true

        delayInt 10
        isStarted p false
        isOpen p false
        parentsAreActive p false
        
      it "if program does not end on its own, then no stop occurs" do
        p <- new' do never
        start p
        isStarted p true
        
        delayInt 10
        isStarted p true
        isOpen p true
        parentsAreActive p true
        
      it "if program does not end on its own, external stop can be used" do
        p <- new' do never
        start p
        isStarted p true
        
        externalStop p
        delayInt 10
        isStarted p false
        isOpen p false
        parentsAreActive p false

  where
  new = Props.new
  
  new' = Props.new' 
  
  start = Program.start
  internalStop = Program.internalStop
  externalStop = Program.externalStop
  
  isStarted = Props.isStarted
  isOpen = Props.isOpen
  parentsAreActive = Props.parentsAreActive
    
  
