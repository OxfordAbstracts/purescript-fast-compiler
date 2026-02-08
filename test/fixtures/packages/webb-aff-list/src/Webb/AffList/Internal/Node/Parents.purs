module Webb.AffList.Internal.Node.Parents where

import Prelude
import Webb.State.Prelude

import Data.Foldable as Fold
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (class MonadEffect)
import Webb.AffList.Data.Node.Parent (class Parent, Parent_)
import Webb.AffList.Data.Node.Parent as Parent
import Webb.AffList.Data.Node.Parents as Parents
import Webb.AffList.Internal.Node.State (NodeState)


type Parents a = NodeState a

-- Stop all the parents of this node, commanding them to cancel.
stop :: forall a m. MonadAff m => Parents a -> m Unit
stop state = liftAff do 
  ps <- aread state.parents
  Fold.for_ ps \parent -> do
    Parent.cancel parent

addParent :: forall a p m. MonadEffect m => Parent p =>
  Parents a -> p -> m Unit
addParent state p = do Parents.addParent p :> state.parents

parents :: forall a m. MonadEffect m =>
  Parents a -> m (Array Parent_)
parents state = do aread state.parents

parentCount :: forall a m. MonadEffect m =>
  Parents a -> m Int
parentCount state = do Parents.size <: state.parents

