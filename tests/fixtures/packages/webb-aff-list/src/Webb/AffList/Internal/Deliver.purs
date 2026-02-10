module Webb.AffList.Internal.Deliver where

import Prelude

import Effect.Aff.Class (class MonadAff)
import Effect.Class (class MonadEffect)
import Webb.Channel as Chan
import Webb.Channel.Data.CMaybe as CMaybe
import Webb.Monad.Prelude (notM, (&&=))
import Webb.Result as Result

{- Represents the general concept of delivery -}


type Deliver a = 
  { value :: Chan.Chan a
  , resume :: Chan.Chan Unit
  }
  

newDeliver :: forall m a . MonadEffect m => m (Deliver a)
newDeliver = do
  value <- Chan.newChan $ Chan.finite 0
  resume <- Chan.newChan $ Chan.finite 0
  pure $ { value, resume }

-- Only sends. Does not pause and wait for resumption -- the machine is probably
-- broken.
sendOnly :: forall m a. MonadAff m => Deliver a -> a -> m Boolean
sendOnly s val = do Chan.send s.value val
  
-- Send a value. Return whether we succeeded, and whether we received a response.
-- If we failed or did not receive a response, the ability to deliver has died.
send :: forall m a. MonadAff m => Deliver a -> a -> m Boolean
send s val = do 
  success <- Chan.send s.value val
  if success then do 
    mval <- Chan.receive s.resume
    pure $ CMaybe.isOpen mval
  else do 
    pure false
    
-- Attempt to receive a value. And if the sender is waiting to resume, notify
-- them that it is indeed okay to resume.
receive :: forall m a. MonadAff m => Deliver a -> m (CMaybe.CMaybe a)
receive s = do 
  Result.yield -- Ensure 'send' has a chance to wait for a resume.
  void $ Chan.trySend s.resume unit
  Chan.receive s.value

close :: forall m a. MonadEffect m => Deliver a -> m Unit
close s = do 
  Chan.close s.value
  Chan.close s.resume

isOpen :: forall m a. MonadEffect m => Deliver a -> m Boolean
isOpen s = Chan.isOpen s.value &&= Chan.isOpen s.resume

isClosed :: forall m a. MonadEffect m => Deliver a -> m Boolean
isClosed s = notM $ isOpen s