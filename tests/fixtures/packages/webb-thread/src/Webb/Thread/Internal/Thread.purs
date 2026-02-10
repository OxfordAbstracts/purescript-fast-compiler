module Webb.Thread.Internal.Thread where

import Prelude
import Webb.State.Prelude

import Data.Foldable (for_)
import Effect.Aff (Aff)
import Effect.Class (class MonadEffect, liftEffect)
import Webb.Monad.Prelude (_kill, launch, notM)
import Webb.Mutex (Mutex, newMutex)
import Webb.Mutex as Mutex
import Webb.Thread.Data.Thread as Thread


{- A thread. Stores a program, and allows us to start/stop running it. -}

type Thread = 
  { state :: ShowRef Thread.Thread
  , program :: ShowRef (Aff Unit)
  , mutex :: Mutex
  }
  
newThread :: forall m. MonadEffect m => m Thread
newThread = liftEffect do 
  state <- newShowRef Thread.Stopped
  program <- newShowRef (pure unit)
  mutex <- newMutex
  pure { state, program, mutex }
  
setProgram :: forall m. MonadEffect m => Thread -> Aff Unit -> m Unit
setProgram t prog = (t.program := prog)

start :: Thread -> Aff Unit
start t = Mutex.locking t.mutex do
  whenM (isStopped t) do
    Thread.starting :> t.state
    program <- aread t.program
    fiber <- launch do 
      program

      -- If the fiber terminates on its own, it will remove itself from the state
      Thread.stop :> t.state
      
    -- This will only store the fiber if we're still starting.
    Thread.running fiber :> t.state
    
stop :: Thread -> Aff Unit
stop t = Mutex.locking t.mutex do
  whenM (isStarted t) do
    mfiber <- Thread.fiber <: t.state
    for_ mfiber \fiber -> do
      _kill fiber
      Thread.stop :> t.state
  
isStarted :: forall m. MonadEffect m => Thread -> m Boolean
isStarted t = do notM (Thread.isStopped <: t.state)

isStopped :: forall m. MonadEffect m => Thread -> m Boolean
isStopped t = do Thread.isStopped <: t.state