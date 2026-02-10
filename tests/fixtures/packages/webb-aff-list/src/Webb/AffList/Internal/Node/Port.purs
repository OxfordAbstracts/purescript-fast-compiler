module Webb.AffList.Internal.Node.Port where

import Prelude
import Webb.State.Prelude

import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (class MonadEffect)
import Effect.Exception (Error)
import Webb.AffList.Data.Node.Port (PortValue)
import Webb.AffList.Data.Node.Port as Port
import Webb.AffList.Data.Node.Port as PortValue
import Webb.AffList.Internal.Deliver as Deliver
import Webb.AffList.Internal.Node.Program as Program
import Webb.AffList.Internal.Node.State (NodeState)
import Webb.Channel.Data.CMaybe as CMaybe

{-
The Port properties of the node state.
-}

type Port a = NodeState a
  
-- Send a value into the port. Don't return after the send -- only return when told
-- that the next value is being requested.
send :: forall m a. MonadAff m => Port a -> a -> m Boolean
send state val = liftAff do 
  Program.start state
  Deliver.send state.deliver (PortValue.Value val)
  
-- Request a value from the port. Ensure the node is started, so that it will generate values, 
-- and ensure the node, if it was suspended, gets unsuspended. 
-- Then attempt to receive a value from the port. 
receive :: forall m a. MonadAff m => Port a -> m (PortValue a)
receive state = liftAff do 
  Program.start state
  cmaybe <- Deliver.receive state.deliver
  case cmaybe of 
    CMaybe.Closed -> do 
      pure Port.Closed
    CMaybe.Open val -> do 
      pure val
      
-- Deliver an error. Since we erred, there's no recovering, and we don't expect the caller
-- to cause use to 'resume'.
error :: forall m a. MonadAff m => Port a -> Error -> m Boolean
error state e = liftAff do 
  Program.start state
  Deliver.sendOnly state.deliver (PortValue.Err e)

-- Close the port in both directions. Ensure that no matter who is waiting, they will be
-- informed of the closure.
close :: forall m a. MonadEffect m => Port a -> m Unit
close state = do Deliver.close state.deliver
      
isOpen :: forall m a. MonadEffect m => Port a -> m Boolean
isOpen state = Deliver.isOpen state.deliver

isClosed :: forall m a. MonadEffect m => Port a -> m Boolean
isClosed state = Deliver.isClosed state.deliver
      