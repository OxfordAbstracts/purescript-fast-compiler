module Data.HugeNum.Gen where

import Prelude

import Control.Monad.Gen as Gen
import Data.HugeNum (HugeNum)
import Data.HugeNum as HugeNum
import Data.Int as Int

genHugeNum :: forall m. Gen.MonadGen m => m HugeNum
genHugeNum = do
  i <- Int.toNumber <$> Gen.chooseInt 0 1000
  d <- Int.toNumber <$> Gen.chooseInt 0 10
  pure $ HugeNum.fromNumber (i + d / 10.0)
