module Webb.AffList.Monad.Yield where

import Prelude
import Webb.State.Prelude

import Control.Monad.Error.Class (class MonadError, class MonadThrow)
import Control.Monad.State (StateT, evalStateT, runStateT)
import Data.Newtype (class Newtype, wrap)
import Effect (Effect)
import Effect.Aff (Aff, Error)
import Effect.Aff as Aff
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (class MonadEffect, liftEffect)
import Webb.AffList.Data.Node.Parent (class Parent, Parent_)
import Webb.AffList.Data.Node.Parent as Parent
import Webb.AffList.Internal.Node as Node
import Webb.Monad.Prelude as Monad


{- The Yield monad enables users to 'yield' values to the output, and to 
  run Aff actions, and correctly launch AffLists so that we can go through
  all values in a list and modify them before yielding them again.
-}


type State a =
  { yield :: a -> Aff Unit
  , addParent :: Parent_ -> Effect Unit
  }
  
newtype Yield v a = Y (StateT (State v) Aff a)

derive newtype instance Functor (Yield v)
derive newtype instance Apply (Yield v)
derive newtype instance Applicative (Yield v)
derive newtype instance Bind (Yield v)
derive newtype instance Monad (Yield v)
derive newtype instance MonadThrow Error (Yield v)
derive newtype instance MonadError Error (Yield v)
derive newtype instance MonadEffect (Yield v)
derive newtype instance MonadAff (Yield v)
derive instance Newtype (Yield v a) _

-- Yield a value to the outer context, and pause until it's time to resume again.
yield :: forall v. v -> Yield v Unit
yield v = wrap do
  this <- mread
  liftAff do this.yield v
  
addParent :: forall v p. Parent p => p -> Yield v Unit
addParent p = wrap do
  this <- mread
  liftEffect do this.addParent (Parent.wrap p)

-- Turn the yielding program into a Node, that can be used as part of AffList programs.
runToNode :: forall m v. MonadEffect m => Yield v Unit -> m (Node.Node v)
runToNode (Y prog) = do
  node <- Node.newNode
  
  let state = 
        { yield: \a -> void (Node.send node a) 
        , addParent: \p -> Node.addParent node p
        } :: State v
      aff = void (runStateT prog state) :: Aff Unit

  Node.setProgram node aff
  pure node
  
asAff :: forall v a. Yield v a -> Yield v (Aff a)
asAff (Y prog) = wrap do 
  state <- mread
  let aff = evalStateT prog state
  pure aff
  
finally :: forall v a. Yield v Unit -> Yield v a -> Yield v a
finally final prog = do 
  final' <- asAff final
  prog' <- asAff prog
  liftAff do Aff.finally final' prog'

onCancel :: forall v a. Yield v Unit -> Yield v a -> Yield v a
onCancel final prog = do 
  final' <- asAff final
  prog' <- asAff prog
  liftAff do Monad.onCancel final' prog'