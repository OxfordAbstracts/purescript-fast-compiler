module Test where

import MyWriter

-- The SpecT-like type: w is fixed (String), m is polymorphic
type MySpecT m a = MyWriterT String m a

-- This function takes MyMonad constraint and uses myTell internally
-- Expected: pending(dictMyMonad) { myTell(myTellWriterT(myMonoidString)(dictMyMonad))(items) }
-- Bug:      pending(dictMyMonad) { myTell(myTellWriterT)(items) } — missing both dict args
pending :: forall m. MyMonad m => String -> MySpecT m String
pending items = myTell items

-- Concrete use: call pending with MyIdentity as the monad
-- This exercises the generated code at runtime
result :: MyWriterT String MyIdentity String
result = pending "hello"

test = unwrapWriterT result
-- TEST: "hello"
