module Webb.Channel.Internal.Channel where

import Prelude

import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)
import Effect.Class (class MonadEffect)
import Webb.Channel.Data.CMaybe (CMaybe)
import Webb.Channel.Data.CMaybe as CMaybe
import Webb.Channel.Internal.Closer as Closer
import Webb.Channel.Internal.Receiver as Receiver
import Webb.Channel.Internal.Sender as Sender
import Webb.Channel.Internal.State (CState)
import Webb.Channel.Internal.State as State
import Webb.Monad.Prelude (notM, (||=))

{- Channel internal functions.
-}

type Channel = CState

-- Sending a value may hang, because if the buffer is full, we
-- have to wait, in order, for the send to complete.
-- We fail to send when the channel is closed; otherwise, we wait
-- and see whether we succeed.
send :: forall a. Channel -> a -> Aff Boolean
send chan a = do
  ifM (isOpen chan) (do
    s <- Sender.new chan
    success <- _sendImmediate s a 
    if success then do
      pure true
    else do 
      Sender.wait s a
  ) (do
    pure false
  )
  
_sendImmediate :: forall m a. MonadEffect m => 
  Sender.Sender -> a -> m Boolean
_sendImmediate s a = do 
  Sender.send s a ||= Sender.tryBuffer s a

-- Receiving a value may hang, because if no value is present to
-- take, then we have to wait for a value.
receive :: forall a. Channel -> Aff (CMaybe a)
receive chan = do 
  r <- Receiver.new chan
  mvalue <- Receiver.receive r
  case mvalue of
    -- Did we receive a value immediately?
    Just value -> do
      pure $ CMaybe.Open value
    Nothing -> do
      mvalue' <- Receiver.wait r
      case mvalue' of
        -- Did we receive a value later?
        Nothing -> do 
          pure CMaybe.Closed
        Just value -> do 
          pure $ CMaybe.Open value

-- Close the channel. Pending and future sends will fail with a boolean flag.
-- Buffered sends will succeed and will continue to be received by any
-- receivers. Once the send buffer is empty, pending and future receivers
-- will only take a "Closed" value from the buffer.
close :: forall m. MonadEffect m => Channel -> m Unit
close chan = do
  c <- Closer.new chan
  Closer.close c
  
-- Try to send the value immediately. Return whether we could do
-- so or not. Does not distinguish between reason for failure
-- (closed, or needed to wait)
trySend :: forall a m. MonadEffect m => Channel -> a -> m Boolean
trySend chan a = do
  ifM (isOpen chan) (do 
    s <- Sender.new chan
    _sendImmediate s a
  ) (do 
    pure false 
  )
  
-- Try to receive a value immediately if there's anything in the queue.
-- No waiting is involved. Closing does not affect this -- we can always
-- try to receive from a closed channel; we just might not succeed.
tryReceive :: forall a m. MonadEffect m => Channel -> m (Maybe a)
tryReceive chan = do
  r <- Receiver.new chan
  Receiver.receive r

isOpen :: forall m. MonadEffect m => Channel -> m Boolean
isOpen chan = State.isOpen chan

isClosed :: forall m. MonadEffect m => Channel -> m Boolean
isClosed chan = notM $ isOpen chan
