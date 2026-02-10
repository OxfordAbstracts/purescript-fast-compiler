module Webb.Channel.Internal.Receiver where

import Prelude
import Webb.State.Prelude

import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype, unwrap, wrap)
import Effect.Aff (Aff)
import Effect.Class (class MonadEffect, liftEffect)
import Webb.Channel.Data.ReceiveItem as RItem
import Webb.Channel.Data.ReceiveQueue as RQueue
import Webb.Channel.Data.SendItem (unvoided)
import Webb.Channel.Data.SendItem as SItem
import Webb.Channel.Data.SendQueue as SQueue
import Webb.Channel.Internal.State (CState)
import Webb.Channel.Internal.State as State
import Webb.Monad.Prelude (forceMaybe', onCancel, (||=))
import Webb.Result as Result


newtype Receiver = R CState

derive instance Newtype Receiver _

new :: forall m. MonadEffect m => CState -> m Receiver
new state = do pure $ wrap state

getThis :: forall m. MonadEffect m => Receiver -> m CState
getThis r = do pure $ unwrap r

receive :: forall m a. MonadEffect m => Receiver -> m (Maybe a)
receive r = do 
  ifM (hasReceivers ||= noSender) (do 
    pure Nothing  
  ) (do 
    s <- nextSender 
    notifySender s 
    pure $ Just (unvoided $ SItem.value s)
  )
  where
  hasReceivers :: m Boolean
  hasReceivers = do
    this <- getThis r
    State.hasReceivers this
    
  noSender = do
    this <- getThis r
    SQueue.isEmpty <: this.senders
    
  nextSender = do
    this <- getThis r
    mitem <- SQueue.first <: this.senders
    SQueue.drop 1 :> this.senders
    forceMaybe' "No first sender" mitem # liftEffect
  
  notifySender item = do
    let result = SItem.result item
    Result.return result true
    
-- Wait in the queue to be delivered a value. If the channel is closed,
-- the receiver will receive nothing if it cannot be matched to a 
-- remaining value in the buffer.
wait :: forall a. Receiver -> Aff (Maybe a)
wait r = do
  ifM (isClosed) (do 
    -- We already failed to get the value immediately, so we know
    -- there are no senders.
    -- So if it's closed, then a sender will never come.
    pure Nothing 
  ) (do 
    item <- buildItem
    enqueue item
    mresult <- await item
    pure $ unvoided <$> mresult
  )
  
  where
  isClosed = do
    this <- getThis r
    State.isClosed this

  buildItem = do
    this <- getThis r
    id <- State.nextId this
    result <- Result.newResult
    let item = RItem.newItem id result
    pure item
    
  enqueue item = do
    this <- getThis r
    RQueue.addLast item :> this.receivers
    
  await item = do
    let result = RItem.result item
    onCancel (remove item)  do
      Result.await result
      
  remove item = do
    this <- getThis r
    let id = RItem.id item
    RQueue.removeId id :> this.receivers
