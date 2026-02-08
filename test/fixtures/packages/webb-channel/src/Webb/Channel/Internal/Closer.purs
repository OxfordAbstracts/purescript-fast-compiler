module Webb.Channel.Internal.Closer where

import Prelude
import Webb.State.Prelude

import Data.Foldable as Fold
import Data.Maybe (Maybe(..))
import Effect.Class (class MonadEffect)
import Webb.Channel.Data.ReceiveItem as RItem
import Webb.Channel.Data.ReceiveQueue as RQueue
import Webb.Channel.Data.SendItem as SItem
import Webb.Channel.Data.SendQueue as SQueue
import Webb.Channel.Internal.State (CState)
import Webb.Channel.Internal.State as State
import Webb.Monad.Prelude (expectM, notM, (&&=))
import Webb.Result as Result


newtype Closer = C CState

new :: forall m. MonadEffect m => CState -> m Closer
new state = do pure $ C state

getThis :: forall m. MonadEffect m => Closer -> m CState
getThis (C state) = do pure state

close :: forall m. MonadEffect m => Closer -> m Unit
close c = do
  this <- getThis c
  whenM isOpen do
    this.open := false
    validate
    whenM onlySenders do closeSenders
    whenM onlyReceivers do closeReceivers
    
  where     
  isOpen = do
    this <- getThis c
    State.isOpen this
    
  validate = do 
    this <- getThis c
    let valid = notM (State.hasSenders this &&= State.hasReceivers this)
    expectM valid "Should not have both senders and receivers"
    
  onlySenders = do 
    this <- getThis c
    State.hasSenders this
    
  closeSenders = do 
    this <- getThis c
    pending <- SQueue.pending <: this.senders
    SQueue.removePending :> this.senders
    Fold.for_ pending closeSender
    
  closeSender item = do
    let result = SItem.result item
    Result.return result false -- indicate the send failed
    
  onlyReceivers = do 
    this <- getThis c
    State.hasReceivers this
    
  closeReceivers = do 
    this <- getThis c
    pending <- RQueue.toArray <: this.receivers
    this.receivers := RQueue.newQueue
    Fold.for_ pending closeReceiver
    
  closeReceiver item = do 
    let result = RItem.result item
    Result.return result Nothing
    

