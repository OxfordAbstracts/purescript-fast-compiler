module OverlapLocalTypeShadow where

import OverlapLocalTypeShadow.Dep (class MyTrans)

-- This module defines its own ListT while a different ListT instance
-- may exist in the imported registry. The overlap check should not
-- trigger a false positive for same-named types from different modules.
data ListT m a = ListT (m a)

instance myTransListT :: MyTrans ListT where
  lift = ListT
