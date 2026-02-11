module Golem.Fetch.URL ( module Output
                       , fromString
                       , traceShow
                       , hash
                       , setHash
                       , hash'
                       , setHash'
                       , host
                       , setHost
                       , hostname
                       , setHostname
                       , href
                       , setHref
                       , origin
                       , password
                       , password'
                       , setPassword
                       , setPassword'
                       , pathname
                       , setPathname
                       , port
                       , setPort
                       , protocol
                       , setProtocol
                       , search
                       , setSearch
                       , searchParams
                       , setSearchParams
                       , username
                       , username'
                       , setUsername
                       , setUsername'
                       , class ToURL
                       , toURL
                       ) where

import Prelude

import Data.Maybe (Maybe(..), fromMaybe)
import Golem.Fetch.Unsafe.URL (URL) as Output
import Golem.Fetch.Unsafe.URL as URL

checkEmptyString :: String -> Maybe String
checkEmptyString "" = Nothing
checkEmptyString s = Just s

maybeEmptyString :: Maybe String -> String
maybeEmptyString = fromMaybe ""

fromString :: String -> URL.URL
fromString = URL._url_make

traceShow :: URL.URL -> URL.URL
traceShow = URL._url_traceShow

hash :: URL.URL -> String
hash = URL._url_hash

setHash :: String -> URL.URL -> URL.URL
setHash = URL._url_setHash

hash' :: URL.URL -> Maybe String
hash' = checkEmptyString <<< hash

setHash' :: Maybe String -> URL.URL -> URL.URL
setHash' s = setHash $ maybeEmptyString s

host :: URL.URL -> String
host = URL._url_host

setHost :: String -> URL.URL -> URL.URL
setHost = URL._url_setHost

hostname :: URL.URL -> String
hostname = URL._url_hostname

setHostname :: String -> URL.URL -> URL.URL
setHostname = URL._url_setHostname

href :: URL.URL -> String
href = URL._url_href

setHref :: String -> URL.URL -> URL.URL
setHref = URL._url_setHref

origin :: URL.URL -> String
origin = URL._url_origin

password :: URL.URL -> String
password = URL._url_password

password' :: URL.URL -> Maybe String
password' = checkEmptyString <<< password

setPassword :: String -> URL.URL -> URL.URL
setPassword = URL._url_setPassword

setPassword' :: Maybe String -> URL.URL -> URL.URL
setPassword' s = setPassword $ maybeEmptyString s

pathname :: URL.URL -> String
pathname = URL._url_pathname

setPathname :: String -> URL.URL -> URL.URL
setPathname = URL._url_setPathname

port :: URL.URL -> String
port = URL._url_port

setPort :: String -> URL.URL -> URL.URL
setPort = URL._url_setPort

protocol :: URL.URL -> String
protocol = URL._url_protocol

setProtocol :: String -> URL.URL -> URL.URL
setProtocol = URL._url_setProtocol

search :: URL.URL -> String
search = URL._url_search

setSearch :: String -> URL.URL -> URL.URL
setSearch = URL._url_setSearch

searchParams :: URL.URL -> URL.URLSearchParams
searchParams = URL._url_searchParams

setSearchParams :: URL.URLSearchParams -> URL.URL -> URL.URL
setSearchParams s = setSearch $ show s

username :: URL.URL -> String
username = URL._url_username

username' :: URL.URL -> Maybe String
username' = checkEmptyString <<< username

setUsername :: String -> URL.URL -> URL.URL
setUsername = URL._url_setUsername

setUsername' :: Maybe String -> URL.URL -> URL.URL
setUsername' s = setUsername $ maybeEmptyString s

class ToURL a where
  toURL :: a -> URL.URL

instance ToURL URL.URL where
  toURL = identity

instance ToURL String where
  toURL = fromString
