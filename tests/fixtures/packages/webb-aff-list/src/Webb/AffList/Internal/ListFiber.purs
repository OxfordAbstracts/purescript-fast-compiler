module Webb.AffList.Internal.ListFiber where

import Prelude
import Webb.State.Prelude

import Control.Monad.Error.Class (throwError)
import Control.Monad.Loops (whileJust_, whileM_)
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (class MonadEffect)
import Webb.AffList.Data.Node.Parent as Parent
import Webb.AffList.Data.Node.Port as PV
import Webb.AffList.Internal.Node as Node
import Webb.Channel.Data.CMaybe as CMaybe
import Webb.Monad.Prelude ((&&=))
import Webb.Stateful (localEffect)



{- 
The ListFiber is to the AffList what the Fiber is to Aff. 
It provides the ability to _cancel_ the entire list computation, and to retrieve 
values from it (while values still are available). Nothing else can be done with it.
-}

newtype ListFiber a = L 
  { node :: Node.Node a
  }
  
type LFiber = ListFiber

instance Show (ListFiber a) where show _ = "ListFiber"

instance Parent.Parent (ListFiber a) where
  cancel list = kill list
  
newListFiber :: forall m a. MonadEffect m => Node.Node a -> m (ListFiber a)
newListFiber node = do 
  pure $ L { node }
  
kill :: forall m a . MonadAff m => LFiber a -> m Unit
kill (L s) = Node.stop s.node

-- Receive the value. Throw if there is an error.
receive :: forall m a. MonadAff m => LFiber a -> m (CMaybe.CMaybe a)
receive (L s) = liftAff do
  pvalue <- Node.receive s.node
  case pvalue of 
    PV.Err e -> do 
      throwError e
    PV.Closed -> do 
      pure $ CMaybe.Closed
    PV.Value v -> do 
      pure $ CMaybe.Open v

-- Receive the value, including if there is an error.
receive' :: forall m a. MonadAff m => LFiber a -> m (PV.PortValue a)
receive' (L s) = liftAff do Node.receive s.node

-- Run code for every item in the aff list.
forEach_ :: forall m a. MonadAff m => LFiber a -> (a -> m Unit) -> m Unit
forEach_ fiber f = do
  whileJust_ (_receive) f
  where
  _receive :: m (Maybe a) 
  _receive = do 
    cmaybe <- receive fiber
    case cmaybe of 
      CMaybe.Closed -> pure Nothing
      CMaybe.Open val -> pure $ Just val
      
-- While the condition holds and while more items remain, read an item and do something
-- with it.
while_ :: forall m a. MonadAff m => LFiber a -> (m Boolean) -> (a -> m Unit) -> m Unit
while_ fiber cond f = do 
  whileM_ (cond &&= shouldContinue) do
    ma <- receive fiber
    case ma of
      CMaybe.Closed -> do 
        continue := false 
      CMaybe.Open a -> do 
        f a
        continue := true
  where
  continue = localEffect do newShowRef true
  shouldContinue = aread continue