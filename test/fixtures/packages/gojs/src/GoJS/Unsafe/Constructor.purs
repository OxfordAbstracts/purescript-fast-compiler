module GoJS.Unsafe.Constructor where

import Effect (Effect)

-- First argument is Class name
foreign import constructor0 :: forall n. String -> Effect n
foreign import constructor1 :: forall n arg1. String -> arg1 -> Effect n
foreign import constructor2 :: forall n arg1 arg2. String -> arg1 -> arg2 -> Effect n
foreign import constructor3 :: forall n arg1 arg2 arg3. String -> arg1 -> arg2 -> arg3 -> Effect n
foreign import constructor4 :: forall n arg1 arg2 arg3 arg4. String -> arg1 -> arg2 -> arg3 -> arg4 -> Effect n
foreign import constructor5 :: forall n arg1 arg2 arg3 arg4 arg5. String -> arg1 -> arg2 -> arg3 -> arg4 -> arg5 -> Effect n
