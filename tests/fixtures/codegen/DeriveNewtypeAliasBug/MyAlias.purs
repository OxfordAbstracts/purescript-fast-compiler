module MyAlias where

import MyTrans (MyTrans)

-- Type alias defined in a separate module
-- When the codegen can't find this alias cross-module, it generates wrong instance names
type MyAlias = MyTrans Array
