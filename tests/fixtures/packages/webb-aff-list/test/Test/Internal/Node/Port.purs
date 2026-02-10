module Test.Internal.Node.Port where

import Test.Prelude

import Effect.Aff (Aff)
import Webb.AffList.Internal.Node.Port as Port
import Webb.AffList.Internal.Node.State as State
import Webb.Thread as Thread


type PortProps = Unit

type State a = State.NodeState a


new :: forall a. Aff (State a)
new = do 
  state <- State.new
  pure state

-- Install a program into the port that has access to the state.
new' :: forall a. (State a -> Aff Unit) -> Aff (State a)
new' f = do 
  state <- State.new
  Thread.setProgram state.thread (f state)
  pure state
  
isOpen :: forall a. State a -> Boolean -> Aff Unit
isOpen state flag = do 
  Port.isOpen state ?= flag
