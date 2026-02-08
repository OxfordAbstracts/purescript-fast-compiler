module GoJS.Key where

import Data.Function.Uncurried (runFn2)
import Unsafe.Coerce (unsafeCoerce)

data Key
  = StringKey String
  | NumberKey Number
  | UndefinedKey

foreign import typeofk :: forall k. k -> String
foreign import undefinedk :: forall k. k

toKey :: forall k. k -> Key 
toKey k = case typeofk k of
  "string" -> StringKey (unsafeCoerce k)
  "number" -> NumberKey (unsafeCoerce k)
  _ -> UndefinedKey

data KeyProperty nodeData k
  = Property String
  | FunctionProperty (Record nodeData -> k -> k)

toKeyProperty :: forall nodeData a @k. a -> KeyProperty nodeData k
toKeyProperty k = case typeofk k of
  "string" -> Property (unsafeCoerce k)
  "function" -> FunctionProperty \objData default -> runFn2 (unsafeCoerce k) objData default
  _ -> Property "" -- Empty string key if the property is not a string or function