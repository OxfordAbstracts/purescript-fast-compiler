module Webb.AffList.Internal.Node where

import Prelude
import Webb.State.Prelude

import Data.Newtype (class Newtype)
import Effect.Aff (Aff)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (class MonadEffect)
import Webb.AffList.Data.Node.Parent as Parent
import Webb.AffList.Data.Node.Port (PortValue)
import Webb.AffList.Internal.Node.Parents (Parents)
import Webb.AffList.Internal.Node.Parents as Parents
import Webb.AffList.Internal.Node.Port (Port)
import Webb.AffList.Internal.Node.Port as Port
import Webb.AffList.Internal.Node.Program (Program)
import Webb.AffList.Internal.Node.Program as Program
import Webb.AffList.Internal.Node.State (class LateNode, NodeState)
import Webb.AffList.Internal.Node.State as State

newtype Node a = N (NodeState a)

instance LateNode (Node a) where
  closePort (N s) = Port.close s
  errorPort (N s) e = void (Port.error s e)

derive instance Newtype (Node a) _

instance Show (Node a) where
  show (N s) = show
    { thread: s.thread
    , parents: s.parents
    , deliver: s.deliver
    , mutex: s.mutex
    , started: s.started
    }

newNode :: forall m a. MonadEffect m => m (Node a)
newNode = do
  state' <- State.new
  let node = N state'
  state'.node := State.wrap node
  pure node
  
-- Set the program. We expect it to write to the node's output via 'send', and
-- to loop recursively if it wants to send multiple values.
setProgram :: forall a m. MonadEffect m => Node a -> Aff Unit -> m Unit
setProgram node prog = do
  p <- program node
  Program.setProgram p prog
  
-- Add a parent to the node. Useful if the node's program is _using_ another List, because
-- this enables us to register the second list as a parent that needs to be cleaned up when
-- the node terminates.
addParent :: forall a m p. MonadEffect m => Parent.Parent p =>
  Node a -> p -> m Unit
addParent node parent = do
  p <- parents node
  Parents.addParent p parent
  
-- Send a normal value into the node. Return whether we succeeded.
send :: forall a m. MonadAff m => Node a -> a -> m Boolean
send node val = do
  p <- port node
  Port.send p val
  
-- Receive a value from the node. If needed, this will _start_ the node itself.
receive :: forall a m. MonadAff m => Node a -> m (PortValue a)
receive node = do 
  p <- port node
  Port.receive p
  
-- Close the node, stopping the program and the port, and stopping the parents
stop :: forall a m. MonadAff m => Node a -> m Unit
stop node = do 
  p <- program node
  Program.externalStop p
  

-------------------- PRIVATE FUNCTIONS ---------------------
-- Not guaranteed to do what you want if you get them and try to use the associated APIs.
------------------------------------------------------------

-- private accessor
port :: forall a m. Monad m => Node a -> m (Port a)
port (N s) = pure s

-- private accessor
program :: forall a m. Monad m => Node a -> m (Program a)
program (N s) = pure s

-- private accessor
parents :: forall a m. Monad m => Node a -> m (Parents a)
parents (N s) = pure s

-- private accessor
state :: forall a m. Monad m => Node a -> m (NodeState a)
state (N s) = pure s