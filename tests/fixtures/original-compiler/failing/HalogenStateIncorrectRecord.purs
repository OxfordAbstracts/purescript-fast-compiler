-- @shouldFailWith TypesDoNotUnify
module HalogenStateIncorrectRecord where

import Prelude

import Control.Applicative.Free (FreeAp, liftFreeAp, hoistFreeAp)
import Control.Monad.Error.Class (class MonadThrow, throwError)
import Control.Monad.Free (Free, hoistFree, liftF)
import Data.Tuple (Tuple)
import Control.Monad.State.Class (class MonadState, modify_)

data HalogenF state action slots output m a = 
  HalogenF (state -> Tuple a state)

newtype HalogenM state action slots output m a = HalogenM (Free (HalogenF state action slots output m) a)


derive newtype instance functorHalogenM :: Functor (HalogenM state action slots output m)
derive newtype instance applyHalogenM :: Apply (HalogenM state action slots output m)
derive newtype instance applicativeHalogenM :: Applicative (HalogenM state action slots output m)
derive newtype instance bindHalogenM :: Bind (HalogenM state action slots output m)
derive newtype instance monadHalogenM :: Monad (HalogenM state action slots output m)
derive newtype instance semigroupHalogenM :: Semigroup a => Semigroup (HalogenM state action slots output m a)
derive newtype instance monoidHalogenM :: Monoid a => Monoid (HalogenM state action slots output m a)

instance MonadState state (HalogenM state action slots output m) where
  state f = HalogenM $ liftF $ HalogenF \s -> f s

type State = { a :: Int } 

handle :: forall m. Int -> HalogenM State Unit Unit Unit m Unit
handle = case _ of
    _ -> do
      modify_ \st ->  st { b = 1 }
        
           