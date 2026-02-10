module Test.Internal.Node where

import Test.Prelude

import Effect.Aff (Aff)
import Test.Internal.Node.Parents as Parents
import Webb.AffList.Internal.Node as Node
import Webb.AffList.Internal.Node.Program as Program



type NodeProps = Unit


new :: forall a. (Node.Node a -> Aff Unit) -> Aff (Node.Node a)
new prog = do 
  node <- Node.newNode
  Node.setProgram node (prog node)
  pure node
  
new' :: forall a. Array Boolean -> Aff (Node.Node a)
new' bools = do 
  node@(Node.N state) <- Node.newNode
  Parents.setFakeParents state bools
  pure node
  
parentsAre :: forall a. Node.Node a -> Array Boolean -> Aff Unit
parentsAre (Node.N state) bools = do 
  Parents.fakeParents state ?= bools

isStarted :: forall a. Node.Node a -> Boolean -> Aff Unit
isStarted node bool = do
  prog <- Node.program node
  Program.isStarted prog ?= bool
  
