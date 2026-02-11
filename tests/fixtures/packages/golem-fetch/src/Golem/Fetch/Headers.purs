module Golem.Fetch.Headers ( module Golem.Fetch.Headers
                           , module Output
                           ) where

import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Golem.Fetch.Unsafe.Fetch (Headers) as Output
import Golem.Fetch.Unsafe.Fetch as F

empty :: F.Headers
empty = F._headers_empty

singleton :: String -> String -> F.Headers
singleton key value = F._headers_make [[key, value]]

fromRecord :: forall r. {|r} -> F.Headers
fromRecord = F._headers_make

insert :: String -> String -> F.Headers -> F.Headers
insert = F._headers_set

append :: String -> String -> F.Headers -> F.Headers
append = F._headers_append

delete :: String -> F.Headers -> F.Headers
delete = F._headers_delete

member :: String -> F.Headers -> Boolean
member = F._headers_has

lookup :: String -> F.Headers -> Maybe String
lookup = F._headers_get Just Nothing

toArray :: F.Headers -> Array (Tuple String String)
toArray = F._headers_entries Tuple

keys :: F.Headers -> Array String
keys = F._headers_keys

values :: F.Headers -> Array String
values = F._headers_values
