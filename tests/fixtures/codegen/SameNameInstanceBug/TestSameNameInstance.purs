module TestSameNameInstance where

import Prelude
import MyBind (class MyBind, myBind)
import MyPipe (MyPipe(..))

-- Uses the parameterized MyBind instance (from MyPipe), not the simple one (from MyBind)
usePipeBind :: forall m a b. Bind m => MyPipe m a -> (a -> MyPipe m b) -> MyPipe m b
usePipeBind = myBind

unwrapPipe :: forall a. MyPipe Array a -> Array a
unwrapPipe (MyPipe xs) = xs

-- TEST: [11,21]
test = unwrapPipe (usePipeBind (MyPipe [10, 20]) (\x -> MyPipe [x + 1]))
