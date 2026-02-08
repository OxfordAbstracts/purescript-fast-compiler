module Node.URL.URLSearchParams
  ( URLSearchParams
  , new
  , fromString
  , fromObject
  , appendParam
  , delete
  , getName
  , getAll
  , has
  , set
  , size
  , sort
  , toString
  , entries
  , keys
  , values
  ) where

import Prelude

import Data.Maybe (Maybe)
import Data.Nullable (Nullable, toMaybe)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Uncurried (EffectFn1, EffectFn2, EffectFn3, runEffectFn1, runEffectFn2, runEffectFn3)
import Foreign (Foreign)

foreign import data URLSearchParams :: Type

foreign import new :: Effect (URLSearchParams)

fromString :: String -> Effect URLSearchParams
fromString str = runEffectFn1 fromStringImpl str

foreign import fromStringImpl :: EffectFn1 (String) (URLSearchParams)

-- | Each label in the record arg must be of type `String`, `Array String`,
-- | or a newtyped version of those two types.
-- | Note: the compiler does not check the record arg to verify that this constraint
-- | has been satisfied.
fromObject
  :: forall r
   . { | r }
  -> Effect URLSearchParams
fromObject obj = runEffectFn1 fromObjectImpl obj

foreign import fromObjectImpl :: forall r. EffectFn1 ({ | r }) (URLSearchParams)

appendParam :: String -> String -> URLSearchParams -> Effect Unit
appendParam name value params = runEffectFn3 appendParamImpl name value params

foreign import appendParamImpl :: EffectFn3 (String) (String) (URLSearchParams) (Unit)

delete :: String -> URLSearchParams -> Effect Unit
delete name params = runEffectFn2 deleteImpl name params

foreign import deleteImpl :: EffectFn2 (String) (URLSearchParams) (Unit)

getName :: String -> URLSearchParams -> Effect (Maybe String)
getName name params = map toMaybe $ runEffectFn2 getNameImpl name params

foreign import getNameImpl :: EffectFn2 (String) (URLSearchParams) (Nullable String)

getAll :: String -> URLSearchParams -> Effect (Array String)
getAll name params = runEffectFn2 getAllImpl name params

foreign import getAllImpl :: EffectFn2 (String) (URLSearchParams) (Array String)

has :: String -> URLSearchParams -> Effect Boolean
has name params = runEffectFn2 hasImpl name params

foreign import hasImpl :: EffectFn2 (String) (URLSearchParams) (Boolean)

set :: String -> String -> URLSearchParams -> Effect Unit
set name value params = runEffectFn3 setImpl name value params

foreign import setImpl :: EffectFn3 (String) (String) (URLSearchParams) (Unit)

size :: URLSearchParams -> Effect Int
size params = runEffectFn1 sizeImpl params

foreign import sizeImpl :: EffectFn1 (URLSearchParams) (Int)

sort :: URLSearchParams -> Effect Unit
sort params = runEffectFn1 sortImpl params

foreign import sortImpl :: EffectFn1 (URLSearchParams) (Unit)

toString :: URLSearchParams -> Effect String
toString params = runEffectFn1 toStringImpl params

foreign import toStringImpl :: EffectFn1 (URLSearchParams) (String)

entries :: URLSearchParams -> Effect (Array (Tuple String Foreign))
entries params = runEffectFn2 entriesImpl params Tuple

foreign import entriesImpl :: forall a b. EffectFn2 URLSearchParams (a -> b -> Tuple a b) (Array (Tuple String Foreign))

keys :: URLSearchParams -> Effect (Array String)
keys params = runEffectFn1 keysImpl params

foreign import keysImpl :: EffectFn1 (URLSearchParams) (Array String)

values :: URLSearchParams -> Effect (Array Foreign)
values params = runEffectFn1 valuesImpl params

foreign import valuesImpl :: EffectFn1 (URLSearchParams) (Array Foreign)
