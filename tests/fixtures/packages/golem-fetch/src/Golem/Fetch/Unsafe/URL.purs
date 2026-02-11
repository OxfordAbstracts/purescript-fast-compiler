module Golem.Fetch.Unsafe.URL where

import Prelude

import Data.Maybe (Maybe)
import Data.Tuple (Tuple)

foreign import data URLSearchParams :: Type

instance Show URLSearchParams where
  show = _search_toString

foreign import _search_empty :: URLSearchParams
foreign import _search_make :: forall a. a -> URLSearchParams
foreign import _search_traceShow :: URLSearchParams -> URLSearchParams
foreign import _search_toString :: URLSearchParams -> String
foreign import _search_append :: String -> String -> URLSearchParams -> URLSearchParams
foreign import _search_delete :: String -> URLSearchParams -> URLSearchParams
foreign import _search_entries :: (String -> String -> Tuple String String) -> URLSearchParams -> Array (Tuple String String)
foreign import _search_get :: (String -> Maybe String) -> Maybe String -> String -> URLSearchParams -> Maybe String
foreign import _search_getAll :: String -> URLSearchParams -> Array String
foreign import _search_has :: String -> URLSearchParams -> Boolean
foreign import _search_keys :: URLSearchParams -> Array String
foreign import _search_set :: String -> String -> URLSearchParams -> URLSearchParams
foreign import _search_size :: URLSearchParams -> Int
foreign import _search_values :: URLSearchParams -> Array String

foreign import data URL :: Type

instance Show URL where
  show = _url_toString

foreign import _url_make :: forall a. a -> URL
foreign import _url_toString :: URL -> String
foreign import _url_traceShow :: URL -> URL
foreign import _url_hash :: URL -> String
foreign import _url_setHash :: String -> URL -> URL
foreign import _url_host :: URL -> String
foreign import _url_setHost :: String -> URL -> URL
foreign import _url_hostname :: URL -> String
foreign import _url_setHostname :: String -> URL -> URL
foreign import _url_href :: URL -> String
foreign import _url_setHref :: String -> URL -> URL
foreign import _url_origin :: URL -> String
foreign import _url_password :: URL -> String
foreign import _url_setPassword :: String -> URL -> URL
foreign import _url_pathname :: URL -> String
foreign import _url_setPathname :: String -> URL -> URL
foreign import _url_port :: URL -> String
foreign import _url_setPort :: String -> URL -> URL
foreign import _url_protocol :: URL -> String
foreign import _url_setProtocol :: String -> URL -> URL
foreign import _url_search :: URL -> String
foreign import _url_setSearch :: String -> URL -> URL
foreign import _url_searchParams :: URL -> URLSearchParams
foreign import _url_username :: URL -> String
foreign import _url_setUsername :: String -> URL -> URL
