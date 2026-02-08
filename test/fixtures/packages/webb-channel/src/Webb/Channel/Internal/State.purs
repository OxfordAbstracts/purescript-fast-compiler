module Webb.Channel.Internal.State where

import Prelude
import Webb.State.Prelude

import Effect.Class (class MonadEffect)
import Webb.Channel.Data.Id (Id)
import Webb.Channel.Data.Id as Id
import Webb.Channel.Data.ReceiveQueue (RQueue)
import Webb.Channel.Data.ReceiveQueue as RQueue
import Webb.Channel.Data.SendQueue (SQueue)
import Webb.Channel.Data.SendQueue as SQueue
import Webb.Monad.Prelude (notM)

type ChannelState = 
  { senders :: ShowRef (SQueue)
  , receivers :: ShowRef (RQueue)
  , open :: ShowRef Boolean
  , id :: ShowRef Id
  }

type CState = ChannelState
  
newState :: forall m . MonadEffect m => 
  SQueue.SendSize -> m (ChannelState)
newState size' = do
  id <- newShowRef $ Id.initial
  senders <- newShowRef $ SQueue.newQueue size'
  receivers <- newShowRef $ RQueue.newQueue
  open <- newShowRef $ true
  pure { senders, open, receivers, id }
  
nextId :: forall m. MonadEffect m => CState -> m Id
nextId this = do 
  current <- aread this.id
  Id.next :> this.id 
  pure current
  
isOpen :: forall m . MonadEffect m => CState -> m Boolean
isOpen this = do aread this.open

isClosed :: forall m . MonadEffect m => CState -> m Boolean
isClosed = notM <<< isOpen

close :: forall m. MonadEffect m => CState -> m Unit
close this = this.open := false

sendSize :: forall m . MonadEffect m => CState -> m Int
sendSize this = SQueue.size <: this.senders

receiveSize :: forall m . MonadEffect m => CState -> m Int
receiveSize this = RQueue.size <: this.receivers
  
hasSenders :: forall m . MonadEffect m => CState -> m Boolean
hasSenders this = notM $ SQueue.isEmpty <: this.senders

hasReceivers :: forall m . MonadEffect m => CState -> m Boolean
hasReceivers this = notM $ RQueue.isEmpty <: this.receivers