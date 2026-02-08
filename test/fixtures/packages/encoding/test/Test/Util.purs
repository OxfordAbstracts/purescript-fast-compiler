module Test.Util
  ( asUint8Array )
where

import Data.ArrayBuffer.Types  ( Uint8Array )
import Data.Function.Uncurried ( Fn1, runFn1 )

asUint8Array :: Array Int -> Uint8Array
asUint8Array arr = runFn1 asUint8ArrayImpl arr

foreign import asUint8ArrayImpl :: Fn1 (Array Int) Uint8Array
