module TestInstanceMethodPointFree where

import Lib

-- Test the point-free instance method (exitCtx).
-- Bug: myModify(myStateStateT) without applying myMonadIdentity.
test :: Array String
test = (runP exitCtx).state
-- TEST: []
