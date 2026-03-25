module MyPipe where

import Prelude
import MyBind (class MyBind)

-- A parameterized type with a same-named instance that takes a dict arg
newtype MyPipe m a = MyPipe (m a)

-- Same instance name as MyBind.myBindProxy but parameterized
instance myBindProxy :: Bind m => MyBind (MyPipe m) where
  myBind (MyPipe ma) f = MyPipe (ma >>= \a -> case f a of MyPipe mb -> mb)
