module Golem.Fetch.URLSearch ( module Golem.Fetch.URLSearch
                             , module Output
                             ) where

import Prelude hiding (append)

import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Golem.Fetch.Unsafe.URL (URLSearchParams) as Output
import Golem.Fetch.Unsafe.URL as URL

traceShow :: URL.URLSearchParams -> URL.URLSearchParams
traceShow = URL._search_traceShow

empty :: URL.URLSearchParams
empty = URL._search_empty

singleton :: String -> String -> URL.URLSearchParams
singleton key value = URL._search_make [[key, value]]

fromString :: String -> URL.URLSearchParams
fromString = URL._search_make

fromArray :: Array (Tuple String String) -> URL.URLSearchParams
fromArray = URL._search_make <<< map \(Tuple a b) -> [a, b]

fromRecord :: forall r. {|r} -> URL.URLSearchParams
fromRecord = URL._search_make

insert :: String -> String -> URL.URLSearchParams -> URL.URLSearchParams
insert = URL._search_set

append :: String -> String -> URL.URLSearchParams -> URL.URLSearchParams
append = URL._search_append

delete :: String -> URL.URLSearchParams -> URL.URLSearchParams
delete = URL._search_delete

member :: String -> URL.URLSearchParams -> Boolean
member = URL._search_has

lookup :: String -> URL.URLSearchParams -> Maybe String
lookup = URL._search_get Just Nothing

lookupElems :: String -> URL.URLSearchParams -> Array String
lookupElems = URL._search_getAll

toArray :: URL.URLSearchParams -> Array (Tuple String String)
toArray = URL._search_entries Tuple

toString :: URL.URLSearchParams -> String
toString = URL._search_toString

keys :: URL.URLSearchParams -> Array String
keys = URL._search_keys

values :: URL.URLSearchParams -> Array String
values = URL._search_values

size :: URL.URLSearchParams -> Int
size = URL._search_size
