module GoJS.EnumValue where

import Prelude

-- This type represents GoJS' EnumValue, but it's never explicitly created in purs. Instead,
-- use enumValueBuilder_ with a class/namespace name and the name of the EnumValue.
foreign import data EnumValue_ :: Type
foreign import enumValueEq :: EnumValue_ -> EnumValue_ -> Boolean

instance Eq EnumValue_ where
  eq = enumValueEq

foreign import enumValueBuilder_ :: String -> String -> EnumValue_
