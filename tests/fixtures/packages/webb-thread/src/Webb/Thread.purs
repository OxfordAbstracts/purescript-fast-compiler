module Webb.Thread where

import Prelude

import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (class MonadEffect, liftEffect)
import Webb.Thread.Internal.Thread as Thread



newtype Thread = T Thread.Thread

instance Show Thread where
  show (T t) = show t.state

newThread :: forall m. MonadEffect m => m Thread
newThread = do 
  t <- Thread.newThread
  pure $ T t
  
runAff :: forall m a. MonadAff m => 
  Thread -> (Thread.Thread -> Aff a) -> m a
runAff (T t) prog = liftAff do prog t

runEffect :: forall m a. MonadEffect m => 
  Thread -> (Thread.Thread -> Effect a) -> m a
runEffect (T t) prog = liftEffect do prog t

setProgram :: forall m. MonadEffect m => Thread -> Aff Unit -> m Unit
setProgram t prog = runEffect t $ 
  \thread -> Thread.setProgram thread prog

start :: forall m. MonadAff m => Thread -> m Unit
start t = runAff t $ 
  \thread -> Thread.start thread

stop :: forall m. MonadAff m => Thread -> m Unit
stop t = runAff t $ 
  \thread -> Thread.stop thread

isStarted :: forall m. MonadEffect m => Thread -> m Boolean
isStarted t = runEffect t $ 
  \thread -> Thread.isStarted thread

isStopped :: forall m. MonadEffect m => Thread -> m Boolean
isStopped t = runEffect t $ 
  \thread -> Thread.isStopped thread