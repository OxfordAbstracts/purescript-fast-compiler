module Webb.Channel 
( module P
, Channel, Chan, newChannel, newChan, send, trySend
, receive, tryReceive, close, isOpen, isClosed, infinite, finite
)
where

import Prelude

import Data.Maybe (Maybe)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (class MonadEffect, liftEffect)
import Webb.Channel.Data.CMaybe (CMaybe)
import Webb.Channel.Data.CMaybe (CMaybe(..)) as P
import Webb.Channel.Data.SendQueue (SendSize)
import Webb.Channel.Data.SendQueue (SendSize(..)) as P
import Webb.Channel.Data.SendQueue as SItem
import Webb.Channel.Internal.Channel as Chan
import Webb.Channel.Internal.State (ChannelState, CState)
import Webb.Channel.Internal.State as State

newtype Channel :: Type -> Type
newtype Channel a = C ChannelState

derive newtype instance Show (Channel a)

type Chan a = Channel a

newChannel :: forall m a. MonadEffect m => SendSize -> m (Channel a)
newChannel size = do 
  state <- State.newState size
  pure $ C state

newChan :: forall m a. MonadEffect m => SendSize -> m (Channel a)
newChan = newChannel
  
send :: forall m a. MonadAff m => Chan a -> a -> m Boolean
send chan a = aff chan $ 
  \state -> Chan.send state a

trySend :: forall m a. MonadEffect m => Chan a -> a -> m Boolean
trySend chan a = eff chan $ 
  \state -> Chan.trySend state a

receive :: forall m a. MonadAff m => Chan a -> m (CMaybe a)
receive chan = aff chan $ 
  \state -> Chan.receive state

tryReceive :: forall m a. MonadEffect m => Chan a -> m (Maybe a)
tryReceive chan = eff chan $ 
  \state -> Chan.tryReceive state
  
close :: forall m a. MonadEffect m => Chan a -> m Unit
close chan = eff chan $
  \state -> Chan.close state

isOpen :: forall m a. MonadEffect m => Chan a -> m Boolean
isOpen chan = eff chan $
  \state -> Chan.isOpen state

isClosed :: forall m a. MonadEffect m => Chan a -> m Boolean
isClosed chan = eff chan $
  \state -> Chan.isClosed state
  
aff :: forall a b m. MonadAff m => 
  Channel a -> (CState -> Aff b) -> m b
aff (C state) prog = liftAff do prog state

eff :: forall a b m. MonadEffect m => 
  Channel a -> (CState -> Effect b) -> m b
eff (C state) prog = liftEffect do prog state
  
infinite :: SendSize
infinite = SItem.Infinite

finite :: Int -> SendSize
finite = SItem.Finite