module Webb.AffList.Internal.Node.State where

import Prelude
import Webb.State.Prelude

import Effect.Aff (Aff, Error)
import Effect.Class (class MonadEffect)
import Unsafe.Coerce (unsafeCoerce)
import Webb.AffList.Data.Node.Parents (Parents)
import Webb.AffList.Data.Node.Parents as Parents
import Webb.AffList.Data.Node.Port (PortValue)
import Webb.AffList.Internal.Deliver (Deliver)
import Webb.AffList.Internal.Deliver as Deliver
import Webb.Mutex (Mutex)
import Webb.Mutex as Mutex
import Webb.Slot (Slot, newSlot)
import Webb.Thread (Thread)
import Webb.Thread as Thread


type NodeState a = 
  { thread :: Thread
  , parents :: ShowRef Parents
  , deliver :: Deliver (PortValue a)
  , node :: Slot LateNode_
  , mutex :: Mutex
  , started :: ShowRef Boolean
  }
  
new :: forall m a. MonadEffect m => m (NodeState a)
new = do
  thread <- Thread.newThread
  started <- newShowRef false
  mutex <- Mutex.newMutex
  parents' <- newShowRef Parents.empty
  deliver' <- Deliver.newDeliver
  node <- newSlot "node's late bindings"
  pure { thread, parents: parents', deliver: deliver', node, started, mutex }
  
  
class LateNode a where
  closePort :: a -> Aff Unit
  errorPort :: a -> Error -> Aff Unit

-- A way to recover the original type unsafely.
unsafeRecover :: forall a. LateNode_ -> a
unsafeRecover (LateNode__ f) = f (\z -> unsafeCoerce z :: a)

newtype LateNode_ = LateNode__ (forall r. (forall z. LateNode z => z -> r) -> r)

wrap :: forall z. LateNode z => z -> LateNode_
wrap z = LateNode__ (_ $ z)

instance LateNode (LateNode_) where 
  closePort (LateNode__ run) = run closePort
  errorPort (LateNode__ run) = run errorPort


