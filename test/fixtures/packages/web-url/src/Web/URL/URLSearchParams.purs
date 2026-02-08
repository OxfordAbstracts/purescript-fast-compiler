module Web.URL.URLSearchParams
  ( URLSearchParams
  , fromString
  , append
  , delete
  , entries
  , get
  , getAll
  , has
  , keys
  , set
  , sort
  , toString
  , values
  )
where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..), fst, snd)

foreign import data URLSearchParams :: Type

instance eqURLSearchParams :: Eq URLSearchParams where
  eq a b = toString a == toString b

instance showURLSearchParams :: Show URLSearchParams where
  show = toString

foreign import urlSearchParamsImpl :: forall a. a -> URLSearchParams
foreign import appendImpl :: String -> String -> URLSearchParams -> URLSearchParams
foreign import deleteImpl :: String -> URLSearchParams -> URLSearchParams
foreign import entriesImpl :: forall a b. (a -> b -> Tuple a b) -> URLSearchParams -> Array (Tuple String String)
foreign import getImpl :: forall a. (a -> Maybe a) -> Maybe a -> String -> URLSearchParams -> Maybe String
foreign import getAllImpl :: String -> URLSearchParams -> Array String
foreign import hasImpl :: String -> URLSearchParams -> Boolean
foreign import setImpl :: String -> String -> URLSearchParams -> URLSearchParams
foreign import sortImpl :: URLSearchParams -> URLSearchParams
foreign import toStringImpl :: URLSearchParams -> String

-- | Create a URLSearchParams from a string which will be parsed from
-- | application/x-www-form-urlencoded format. A leading '?' character is
-- | ignored.
fromString :: String -> URLSearchParams
fromString = urlSearchParamsImpl

-- | Appends a specified key/value pair as a new search parameter.
append :: String -> String -> URLSearchParams -> URLSearchParams
append = appendImpl

-- | Deletes the given search parameter, and its associated value, from the list
-- | of all search parameters.
delete :: String -> URLSearchParams -> URLSearchParams
delete = deleteImpl

-- | Returns an array of all key/value pairs contained in this object.
entries :: URLSearchParams -> Array (Tuple String String)
entries = entriesImpl Tuple

-- | Returns the first value associated with the given search parameter.
get :: String -> URLSearchParams -> Maybe String
get = getImpl Just Nothing

-- | Returns all the values associated with a given search parameter.
getAll :: String -> URLSearchParams -> Array String
getAll = getAllImpl

-- | Returns a Boolean indicating if such a given parameter exists.
has :: String -> URLSearchParams -> Boolean
has = hasImpl

-- | Returns an array of all keys of the key/value pairs contained in this
-- | object.
keys :: URLSearchParams -> Array String
keys = map fst <<< entries

-- | Sets the value associated with a given search parameter to the given value.
-- | If there are several values, the others are deleted.
set :: String -> String -> URLSearchParams -> URLSearchParams
set = setImpl

-- | Sorts all key/value pairs, if any, by their keys.
sort :: URLSearchParams -> URLSearchParams
sort = sortImpl

-- | Returns a string containing a query string suitable for use in a URL.
toString :: URLSearchParams -> String
toString = toStringImpl

-- | Returns an array of all values of the key/value pairs contained in this
-- | object.
values :: URLSearchParams -> Array String
values = map snd <<< entries
