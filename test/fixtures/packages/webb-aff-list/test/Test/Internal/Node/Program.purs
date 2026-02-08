module Test.Internal.Node.Program where

import Test.Prelude

import Data.Maybe (Maybe(..), isJust, isNothing)
import Effect.Aff (Aff, Error)
import Test.Internal.Node.Parents as Parents
import Webb.AffList.Internal.Node.Program as Program
import Webb.AffList.Internal.Node.State as State
import Webb.Array as Array


{- Assistance for creating a Program in a testable state. In particular, this handles the late-binding so that it's testable independently of the Port.
-}


type ProgProps = Unit


newtype FakeLate = F (ShowRef
  { open :: Boolean
  , error :: Maybe Error
  })
  
instance State.LateNode FakeLate where
  closePort (F ref) = (_ { open = false }) :> ref
  errorPort (F ref) err = (_ { error = Just err }) :> ref
  
newFakeLate :: Aff FakeLate
newFakeLate = do 
  ref <- newShowRef { open: true, error: Nothing }
  pure $ F ref

new :: forall a. Aff (State.NodeState a)
new = do 
  state <- State.new
  late <- newFakeLate
  state.node := State.wrap late
  
  -- We have fake parents that are supposed to get stopped.
  Parents.setFakeParents state [true, true, true]
  pure state

-- Set the program, triggering adornments.
new' :: forall a. Aff Unit -> Aff (State.NodeState a)
new' prog = do 
  state <- State.new
  late <- newFakeLate
  state.node := State.wrap late
  
  Program.setProgram state prog
  
  -- We have fake parents that are supposed to get stopped.
  Parents.setFakeParents state [true, true, true]
  pure state
  
recover :: forall a. State.NodeState a -> Aff (FakeLate)
recover state = do 
  node <- aread state.node
  pure $ State.unsafeRecover node

hasError :: forall a. State.NodeState a -> Boolean -> Aff Unit
hasError state flag = do 
  (F ref) <- recover state
  merr <- _.error <: ref
  if flag then do 
    shouldSatisfy merr isJust
  else do 
    shouldSatisfy merr isNothing
    
isOpen :: forall a. State.NodeState a -> Boolean -> Aff Unit
isOpen state flag = do 
  (F ref) <- recover state
  open <- _.open <: ref
  open === flag

isStarted :: forall a. State.NodeState a -> Boolean -> Aff Unit
isStarted state flag = do 
  Program.isStarted state ?= flag

parentsAreActive :: forall a. State.NodeState a -> Boolean -> Aff Unit
parentsAreActive state flag = do 
  arr <- Parents.fakeParents state
  Array.all identity arr === flag