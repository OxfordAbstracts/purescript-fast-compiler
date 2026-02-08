module GoJS.Model.Binding.Static where

import Data.Function.Uncurried (Fn1)
import GoJS.EnumValue (EnumValue_)
import GoJS.Unsafe (callStaticPure1, callStaticPure2)

parseEnum_ :: forall a. a -> EnumValue_ -> Fn1 String EnumValue_
parseEnum_ = callStaticPure2 "Binding" "parseEnum"

toString_ :: forall a. a -> String
toString_ = callStaticPure1 "Binding" "toString"
