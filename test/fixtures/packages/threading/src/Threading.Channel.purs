module Threading.Channel
  ( Channel
  , Sender
  , Receiver
  , recv
  , tryRecv
  , send
  , peek
  , tryPeek
  , channel
  , sender
  , receiver
  ) where

import Prelude

import Control.Monad.Error.Class (throwError)
import Data.Array as Array
import Data.CatList (CatList)
import Data.CatList as CatList
import Data.Either (Either(..))
import Data.Maybe (Maybe(..), isJust, maybe)
import Data.Traversable (for)
import Data.Tuple (fst)
import Data.Tuple.Nested ((/\))
import Data.Witherable (wither)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff as Aff
import Effect.Class (liftEffect)
import Effect.Exception (error)
import JS.WeakRef (WeakRef)
import JS.WeakRef as WeakRef
import Threading.Data.Mutex (Mutex)
import Threading.Data.Mutex as Mutex
import Type.Function (type ($))

-- | A multi-producer multi-consumer channel for communication
-- | between threads.
-- |
-- | Senders will broadcast messages to all living receivers,
-- | doing nothing if there are no receivers.
-- |
-- | Receivers can wait for messages to be sent. Messages that
-- | are sent while the receiver is not waiting will be buffered,
-- | and `recv`d in the order they were sent.
data Channel a = Channel (Mutex $ Array $ WeakRef $ Receiver a)

data Sender a = Sender (Channel a)
data Receiver a = Receiver (Mutex $ Maybe (a -> Effect Unit)) (Mutex $ CatList a)

-- | Create a new channel
channel :: forall a. Effect (Channel a)
channel = do
  recvs <- Mutex.mutex []
  pure $ Channel recvs

-- | Create a new message receiver
receiver :: forall a. Channel a -> Aff (Receiver a)
receiver (Channel recvsRef) = do
  g <- Mutex.lock recvsRef
  liftEffect do
    queue <- Mutex.mutex CatList.empty
    wake <- Mutex.mutex Nothing
    recvs <- Mutex.read g
    let r = Receiver wake queue
    recvWeak <- WeakRef.make r
    Mutex.write g $ Array.cons recvWeak recvs
    Mutex.release g
    pure r

-- | Create a new message sender
sender :: forall a. Channel a -> Effect (Sender a)
sender c = pure $ Sender c

-- | Send a message to all living receivers
send :: forall a. Sender a -> a -> Aff Unit
send (Sender (Channel recvsRef)) a = do
  recvsG <- Mutex.lock recvsRef
  recvWeaks <- liftEffect $ Mutex.read recvsG
  recvs <- liftEffect $ wither WeakRef.deref recvWeaks
  void $ for recvs \(Receiver wakeRef queueRef) -> do
    wakeG <- Mutex.lock wakeRef
    wake <- liftEffect $ Mutex.read wakeG

    queueG <- Mutex.lock queueRef
    head /\ tail <-
      liftEffect (Mutex.read queueG)
        <#> CatList.uncons
        <#> maybe (a /\ CatList.empty) (\(head /\ tail) -> head /\ CatList.snoc tail a)

    let
      q = CatList.cons head tail

    liftEffect do
      maybe (Mutex.write queueG q) (\f -> Mutex.write queueG tail *> f head) wake
      Mutex.release wakeG
      Mutex.release queueG
  liftEffect $ Mutex.release recvsG

-- | Read a queued message and pop it from the queue.
-- |
-- | If no queued messages have been sent, returns Nothing.
tryRecv :: forall a. Receiver a -> Aff (Maybe a)
tryRecv (Receiver _ queueRef) = do
  queueG <- Mutex.lock queueRef
  queueM <- CatList.uncons <$> liftEffect (Mutex.read queueG)
  for queueM \(a /\ tail) -> liftEffect $ Mutex.write queueG tail *> Mutex.release queueG $> a

-- | Block until a message is sent, and pop it from the queue.
-- |
-- | If a message has been sent since the
-- | last call to `recv`, then it will
-- | be immediately popped & returned.
recv :: forall a. Receiver a -> Aff a
recv (Receiver wakeRef queueRef) = do
  wakeG <- Mutex.lock wakeRef
  queueG <- Mutex.lock queueRef
  liftEffect
    $ whenM (isJust <$> Mutex.read wakeG)
    $ throwError
    $ error "Receiver has been shared between multiple fibers, which is not supported."

  queueM <- liftEffect $ CatList.uncons <$> Mutex.read queueG
  case queueM of
    Just (a /\ tail) -> liftEffect do
      Mutex.write queueG tail
      Mutex.release wakeG
      Mutex.release queueG
      pure a
    Nothing -> Aff.makeAff \cb -> do
      Mutex.write wakeG $ Just $ cb <<< Right
      Mutex.release wakeG
      Mutex.release queueG
      pure $ Aff.Canceler $ const $ Mutex.put wakeRef Nothing

-- | Read a queued message without altering the queue.
-- |
-- | If no queued messages have been sent, returns Nothing.
tryPeek :: forall a. Receiver a -> Aff (Maybe a)
tryPeek (Receiver _ queueRef) = map fst <$> CatList.uncons <$> Mutex.get queueRef

-- | Block until a message is sent, and read
-- | it without removing it from the queue.
-- |
-- | If a message has been sent since the
-- | last call to `recv`, then it will
-- | be immediately returned.
peek :: forall a. Receiver a -> Aff a
peek (Receiver wakeRef queueRef) = do
  wakeG <- Mutex.lock wakeRef
  queueM <- CatList.uncons <$> Mutex.get queueRef
  liftEffect
    $ whenM (isJust <$> Mutex.read wakeG)
    $ throwError
    $ error "Receiver has been shared between multiple fibers, which is not supported."

  case queueM of
    Just (a /\ _) -> liftEffect $ Mutex.release wakeG $> a
    Nothing -> Aff.makeAff \cb -> do
      Mutex.write wakeG $ Just $ cb <<< Right
      Mutex.release wakeG
      pure $ Aff.Canceler $ const $ Mutex.put wakeRef Nothing
