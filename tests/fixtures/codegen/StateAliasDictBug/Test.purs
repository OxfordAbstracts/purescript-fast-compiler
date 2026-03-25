module Test where

import MyState

-- Newtype wrapping MyState (like Gen wrapping State)
newtype MyGen a = MyGen (MyState Int a)

-- Point-free value using myState through the newtype
-- Expected: MyGen(myState(myMonadStateMyStateT(myMonadIdentity))(f))
-- Bug:      MyGen(myState(myMonadStateMyStateT)(f)) — missing myMonadIdentity arg
myGet :: MyGen Int
myGet = MyGen (myState (\s -> { state: s, value: s }))

-- Unwrap and run
runGen :: forall a. MyGen a -> Int -> { state :: Int, value :: a }
runGen (MyGen st) = runMyState st

test = (runGen myGet 42).value
-- TEST: 42
