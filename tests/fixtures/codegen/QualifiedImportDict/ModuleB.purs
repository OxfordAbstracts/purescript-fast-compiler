module ModuleB where
-- TEST: 42

import ModuleA as Q

test :: Int
test = Q.unbox (Q.runIt (Q.Box 42))
 