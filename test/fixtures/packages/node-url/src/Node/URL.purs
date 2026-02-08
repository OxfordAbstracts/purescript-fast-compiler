module Node.URL
  ( URL
  , new
  , new'
  , pathToFileURL
  , hash
  , setHash
  , host
  , setHost
  , hostname
  , setHostname
  , href
  , setHref
  , origin
  , password
  , setPassword
  , pathname
  , setPathname
  , port
  , setPort
  , protocol
  , setProtocol
  , search
  , setSearch
  , searchParams
  , username
  , setUsername
  , canParse
  , domainToAscii
  , domainToUnicode
  , fileURLToPath
  , fileURLToPath'
  , UrlFormatOptions
  , format
  , format'
  , pathToFileUrl
  , HttpOptions
  , urlToHTTPOptions
  ) where

import Prelude

import Data.Function.Uncurried (Fn2, runFn2)
import Effect (Effect)
import Effect.Uncurried (EffectFn1, EffectFn2, runEffectFn1, runEffectFn2)
import Node.URL.URLSearchParams (URLSearchParams)
import Prim.Row as Row

foreign import data URL :: Type

instance Show URL where
  show x = "URL(" <> hrefPure x <> ")"

new :: String -> Effect URL
new input = runEffectFn1 newImpl input

foreign import newImpl :: EffectFn1 (String) (URL)

new' :: String -> String -> Effect URL
new' input base = runEffectFn2 newRelativeImpl input base

foreign import newRelativeImpl :: EffectFn2 (String) (String) (URL)

pathToFileURL :: String -> Effect URL
pathToFileURL path = runEffectFn1 pathToFileURLImpl path

foreign import pathToFileURLImpl :: EffectFn1 (String) (URL)

hash :: URL -> Effect String
hash url = runEffectFn1 hashImpl url

foreign import hashImpl :: EffectFn1 URL String

setHash :: String -> URL -> Effect Unit
setHash val url = runEffectFn2 setHashImpl val url

foreign import setHashImpl :: EffectFn2 String URL Unit

host :: URL -> Effect String
host url = runEffectFn1 hostImpl url

foreign import hostImpl :: EffectFn1 URL String

setHost :: String -> URL -> Effect Unit
setHost val url = runEffectFn2 setHostImpl val url

foreign import setHostImpl :: EffectFn2 String URL Unit

hostname :: URL -> Effect String
hostname url = runEffectFn1 hostnameImpl url

foreign import hostnameImpl :: EffectFn1 URL String

setHostname :: String -> URL -> Effect Unit
setHostname val url = runEffectFn2 setHostnameImpl val url

foreign import setHostnameImpl :: EffectFn2 String URL Unit

-- do not export
foreign import hrefPure :: URL -> String

href :: URL -> Effect String
href url = runEffectFn1 hrefImpl url

foreign import hrefImpl :: EffectFn1 URL String

setHref :: String -> URL -> Effect Unit
setHref val url = runEffectFn2 setHrefImpl val url

foreign import setHrefImpl :: EffectFn2 String URL Unit

foreign import origin :: URL -> String

password :: URL -> Effect String
password url = runEffectFn1 passwordImpl url

foreign import passwordImpl :: EffectFn1 URL String

setPassword :: String -> URL -> Effect Unit
setPassword val url = runEffectFn2 setPasswordImpl val url

foreign import setPasswordImpl :: EffectFn2 String URL Unit

pathname :: URL -> Effect String
pathname url = runEffectFn1 pathnameImpl url

foreign import pathnameImpl :: EffectFn1 URL String

setPathname :: String -> URL -> Effect Unit
setPathname val url = runEffectFn2 setPathnameImpl val url

foreign import setPathnameImpl :: EffectFn2 String URL Unit

port :: URL -> Effect String
port url = runEffectFn1 portImpl url

foreign import portImpl :: EffectFn1 URL String

setPort :: String -> URL -> Effect Unit
setPort val url = runEffectFn2 setPortImpl val url

foreign import setPortImpl :: EffectFn2 String URL Unit

protocol :: URL -> Effect String
protocol url = runEffectFn1 protocolImpl url

foreign import protocolImpl :: EffectFn1 URL String

setProtocol :: String -> URL -> Effect Unit
setProtocol val url = runEffectFn2 setProtocolImpl val url

foreign import setProtocolImpl :: EffectFn2 String URL Unit

search :: URL -> Effect String
search url = runEffectFn1 searchImpl url

foreign import searchImpl :: EffectFn1 URL String

setSearch :: String -> URL -> Effect Unit
setSearch val url = runEffectFn2 setSearchImpl val url

foreign import setSearchImpl :: EffectFn2 String URL Unit

searchParams :: URL -> Effect URLSearchParams
searchParams url = runEffectFn1 searchParamsImpl url

foreign import searchParamsImpl :: EffectFn1 (URL) (URLSearchParams)

username :: URL -> Effect String
username url = runEffectFn1 usernameImpl url

foreign import usernameImpl :: EffectFn1 URL String

setUsername :: String -> URL -> Effect Unit
setUsername val url = runEffectFn2 setUsernameImpl val url

foreign import setUsernameImpl :: EffectFn2 String URL Unit

canParse :: String -> String -> Boolean
canParse input base = runFn2 canParseImpl input base

foreign import canParseImpl :: Fn2 (String) (String) (Boolean)

domainToAscii :: String -> Effect String
domainToAscii domain = runEffectFn1 domainToAsciiImpl domain

foreign import domainToAsciiImpl :: EffectFn1 (String) (String)

domainToUnicode :: String -> Effect String
domainToUnicode domain = runEffectFn1 domainToUnicodeImpl domain

foreign import domainToUnicodeImpl :: EffectFn1 (String) (String)

fileURLToPath :: String -> Effect String
fileURLToPath str = runEffectFn1 fileURLToPathImpl str

foreign import fileURLToPathImpl :: EffectFn1 String String

fileURLToPath' :: URL -> Effect String
fileURLToPath' url = runEffectFn1 fileURLToPathUrlImpl url

foreign import fileURLToPathUrlImpl :: EffectFn1 URL String

format :: URL -> Effect String
format url = runEffectFn1 formatImpl url

foreign import formatImpl :: EffectFn1 (URL) (String)

-- | - `auth` <boolean> true if the serialized URL string should include the username and password, false otherwise. Default: true.
-- | - `fragment` <boolean> true if the serialized URL string should include the fragment, false otherwise. Default: true.
-- | - `search` <boolean> true if the serialized URL string should include the search query, false otherwise. Default: true.
-- | - `unicode` <boolean> true if Unicode characters appearing in the host component of the URL string should be encoded directly as opposed to being Punycode encoded. Default: false.
type UrlFormatOptions =
  ( auth :: Boolean
  , fragment :: Boolean
  , search :: Boolean
  , unicode :: Boolean
  )

format'
  :: forall r trash
   . Row.Union r trash UrlFormatOptions
  => URL
  -> { | r }
  -> Effect String
format' url opts = runEffectFn2 formatOptsImpl url opts

foreign import formatOptsImpl :: forall r. EffectFn2 (URL) ({ | r }) (String)

pathToFileUrl :: String -> Effect URL
pathToFileUrl path = runEffectFn1 pathToFileUrlImpl path

foreign import pathToFileUrlImpl :: EffectFn1 (String) (URL)

-- | - `protocol` <string> Protocol to use.
-- | - `hostname` <string> A domain name or IP address of the server to issue the request to.
-- | - `hash` <string> The fragment portion of the URL.
-- | - `search` <string> The serialized query portion of the URL.
-- | - `pathname` <string> The path portion of the URL.
-- | - `path` <string> Request path. Should include query string if any. E.G. '/index.html?page=12'. An exception is thrown when the request path contains illegal characters. Currently, only spaces are rejected but that may change in the future.
-- | - `href` <string> The serialized URL.
-- | - `port` <number> Port of remote server.
-- | - `auth` <string> Basic authentication i.e. 'user:password' to compute an Authorization header.
type HttpOptions =
  { protocol :: String
  , hostname :: String
  , hash :: String
  , search :: String
  , pathname :: String
  , path :: String
  , href :: String
  , port :: Int
  , auth :: String
  }

urlToHTTPOptions :: URL -> Effect HttpOptions
urlToHTTPOptions url = runEffectFn1 urlToHttpOptionsImpl url

foreign import urlToHttpOptionsImpl :: EffectFn1 (URL) (HttpOptions)
