-- @shouldFailWith TypesDoNotUnify
module HalogenStateIncorrectRecordNested where

import Prelude

import Control.Applicative.Free (FreeAp, liftFreeAp, hoistFreeAp)
import Control.Monad.Error.Class (class MonadThrow, throwError)
import Control.Monad.Free (Free, hoistFree, liftF)
import Data.Foldable (any)
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

type State =
  { level1 ::
      { level2 ::
          { level3 ::
              { xs :: Array { b :: Boolean }
              , ys :: Array { prop :: String } 
              }
          }
      }
  , bool :: Boolean
  }

handle :: forall m. Int -> HalogenM State String Int {} m Unit
handle = do 
  go 
  where 
  go = case _ of
    _ -> childAction 
    
  childAction = do
      modify_ \st -> 
        let 
          ok = any _.b st.level1.level2.level3.xs
          notOk = any _.b st.level1.level2.level3.ys
        in 
        st { bool = ok && notOk }


