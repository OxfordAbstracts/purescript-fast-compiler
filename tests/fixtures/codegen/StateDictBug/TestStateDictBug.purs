module TestStateDictBug where

import Prelude
import Data.Newtype (class Newtype, wrap, unwrap)
import StateTrans (StateT(..), State, class MonadState, state, runState, Identity(..))

-- Gen wraps State Int (like Test.QuickCheck.Gen wraps State GenState)
newtype Gen a = Gen (State Int a)

derive instance newtypeGen :: Newtype (Gen a) _

-- Derived newtype instances (like the real Gen)
derive newtype instance functorGen :: Functor Gen
derive newtype instance applyGen :: Apply Gen
derive newtype instance applicativeGen :: Applicative Gen
derive newtype instance bindGen :: Bind Gen
derive newtype instance monadGen :: Monad Gen
derive newtype instance monadStateGen :: MonadState Int Gen

runGen :: forall a. Gen a -> Int -> { value :: a, state :: Int }
runGen (Gen s) = runState s

-- The bug pattern from lcgStep:
-- Gen $ state f where f s = ...
-- This uses `state` through the newtype, which needs
-- monadStateStateT(monadIdentity) but may emit monadStateStateT unapplied.
lcgStep :: Gen Int
lcgStep = Gen $ state f where
  f s = { value: s, state: s + 1 }

-- A second function also using state (like resize/perturbGen)
getState :: Gen Int
getState = state \s -> { value: s, state: s }

test :: Int
test = (runGen lcgStep 42).value
-- TEST: 42
