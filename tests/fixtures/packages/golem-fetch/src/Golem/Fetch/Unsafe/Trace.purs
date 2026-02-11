module Golem.Fetch.Unsafe.Trace where

import Prelude

-- | 类似于Haskell的Debug.Trace之traceShowId。
-- |
-- | `traceShow`内部使用`console.log`打印。
foreign import traceShow :: forall a. a -> a

traceShow' :: forall a. a -> Unit
traceShow' = void traceShow
