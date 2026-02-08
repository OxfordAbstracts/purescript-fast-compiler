module Webb.AffList.Internal.Node.Program where

import Prelude
import Webb.State.Prelude

import Effect.Aff (Aff, catchError)
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (class MonadEffect)
import Webb.AffList.Internal.Node.Parents as Parents
import Webb.AffList.Internal.Node.State (NodeState)
import Webb.AffList.Internal.Node.State as State
import Webb.Mutex as Mutex
import Webb.Thread as Thread


{- Illustrates the behavior of the node as a program that has to be started and stopped.
-}

type Program a = NodeState a

-- Set the node's program. We expect it to run while yielding to the port, but 
-- the programs' definition is outside the scope of what we do here.
setProgram :: forall a m. MonadEffect m => Program a -> Aff Unit -> m Unit
setProgram state prog = do 
  Thread.setProgram state.thread finalProg
  
  where
  finalProg = do 
    catchError (do 
      void $ prog
    ) (\e -> do 
      -- If an error occurred, the error must propagate.
      node <- aread state.node
      State.errorPort node e
    )
    internalStop state

isStarted :: forall a m. MonadEffect m => Program a -> m Boolean
isStarted state = aread state.started

-- Start the program if it hasn't been started yet.
start :: forall a m. MonadAff m => Program a -> m Unit
start state = do 
  Mutex.locking state.mutex do
    unlessM (isStarted state) do
      Thread.start state.thread
      state.started := true


-- Illustrate what it means to _stop_ the program -- cancelling it if it is running,
-- and propagating the error. This is a _normal_ stop, executed from the outside.
-- We only want to start/stop if the program itself is started or stopped.
externalStop :: forall a m. MonadAff m => Program a -> m Unit
externalStop state = liftAff do 
  Mutex.locking state.mutex do 
    whenM (isStarted state) do
      node <- aread state.node
      State.closePort node
      Thread.stop state.thread -- cancel the thread, and let it perform cleanup.
      Parents.stop state
      state.started := false
  
-- An internal stop, executed by the program itself, which is terminating on its own.
internalStop :: forall a m. MonadAff m => Program a -> m Unit
internalStop state = liftAff do 
  Mutex.locking state.mutex do 
    whenM (isStarted state) do
      node <- aread state.node
      State.closePort node
      Parents.stop state 
      state.started := false
  

