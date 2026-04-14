-- @shouldFailWith TypesDoNotUnify
module HalogenStateIncorrectAnnotation where

import Prelude

import Lib as H
import Control.Applicative.Free (FreeAp, hoistFreeAp, liftFreeAp)
import Control.Monad.Error.Class (class MonadThrow, throwError)
import Control.Monad.Free (Free, hoistFree, liftF)
import Control.Monad.State.Class (class MonadState, modify_)
import Data.Tuple (Tuple)

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

test :: forall state action slots output m a. HalogenM state action slots output m Unit
test = do
  H.modify_ \st ->
    st
      { test = 1
      }

