module Golem.Fetch.Request ( RequestCache(..)
                           , RequestCredentials(..)
                           , RequestMethod(..)
                           , RequestMode(..)
                           , RequestPriority(..)
                           , RequestRedirect(..)
                           , RequestBody
                           , RequestRecord
                           , Request(..)
                           , withRequest
                           , setCache
                           , removeCache
                           , setCredentials
                           , removeCredential
                           , setHeaders
                           , appendHeader
                           , removeHeaders
                           , setHeader
                           , setKeepalive
                           , removeKeepalive
                           , setMethod
                           , removeMethod
                           , setMode
                           , removeMode
                           , setPriority
                           , removePriority
                           , setRedirect
                           , removeRedirect
                           , setReferrer
                           , removeReferrer
                           , setBodyJson'
                           , setBodyJson
                           , setBodyForm'
                           , setBodyForm
                           , removeBody
                           , defaultRequest
                           , requestToInit
                           ) where

import Prelude

import Data.Argonaut.Core (Json, stringify)
import Data.Argonaut.Encode (class EncodeJson, encodeJson)
import Data.Maybe (Maybe(..))
import Golem.Fetch.Headers as H
import Golem.Fetch.URLSearch as S
import Golem.Fetch.Unsafe.Fetch as F

data RequestCache = RequestCacheDefault
                  | RequestCacheNoStore
                  | RequestCacheReload
                  | RequestCacheNoCache
                  | RequestCacheForceCache
                  | RequestCacheOnlyIfCached

derive instance Eq RequestCache

instance Show RequestCache where
  show RequestCacheDefault = "RequestCacheDefault"
  show RequestCacheNoStore = "RequestCacheNoStore"
  show RequestCacheReload = "RequestCacheReload"
  show RequestCacheNoCache = "RequestCacheNoCache"
  show RequestCacheForceCache = "RequestCacheForceCache"
  show RequestCacheOnlyIfCached = "RequestCacheOnlyIfCached"

cacheToString :: RequestCache -> String
cacheToString RequestCacheDefault = "default"
cacheToString RequestCacheNoStore = "no-store"
cacheToString RequestCacheReload = "reload"
cacheToString RequestCacheNoCache = "no-cache"
cacheToString RequestCacheForceCache = "force-cache"
cacheToString RequestCacheOnlyIfCached = "only-if-cached"

data RequestCredentials = RequestCredentialsOmit
                        | RequestCredentialsSameOrigin
                        | RequestCredentialInclude

derive instance Eq RequestCredentials

instance Show RequestCredentials where
  show RequestCredentialsOmit = "RequestCredentialsOmit"
  show RequestCredentialsSameOrigin = "RequestCredentialsSameOrigin"
  show RequestCredentialInclude = "RequestCredentialInclude"

credentialsToString :: RequestCredentials -> String
credentialsToString RequestCredentialsOmit = "omit"
credentialsToString RequestCredentialsSameOrigin = "same-origin"
credentialsToString RequestCredentialInclude = "include"

data RequestMethod = RequestGet
                   | RequestHead
                   | RequestPost
                   | RequestPut
                   | RequestDelete
                   | RequestConnect
                   | RequestOptions
                   | RequestTrace
                   | RequestPatch

derive instance Eq RequestMethod

instance Show RequestMethod where
  show RequestGet = "RequestGet"
  show RequestHead = "RequestHead"
  show RequestPost = "RequestPost"
  show RequestPut = "RequestPut"
  show RequestDelete = "RequestDelete"
  show RequestConnect = "RequestConnect"
  show RequestOptions = "RequestOptions"
  show RequestTrace = "RequestTrace"
  show RequestPatch = "RequestPatch"

methodToString :: RequestMethod -> String
methodToString RequestGet = "GET"
methodToString RequestHead = "HEAD"
methodToString RequestPost = "POST"
methodToString RequestPut = "PUT"
methodToString RequestDelete = "DELETE"
methodToString RequestConnect = "CONNECT"
methodToString RequestOptions = "OPTIONS"
methodToString RequestTrace = "TRACE"
methodToString RequestPatch = "PATCH"

data RequestMode = RequestModeSameOrigin
                 | RequestModeCors
                 | RequestModeNoCors

derive instance Eq RequestMode

instance Show RequestMode where
  show RequestModeSameOrigin = "RequestModeSameOrigin"
  show RequestModeCors = "RequestModeCors"
  show RequestModeNoCors = "RequestModeNoCors"

modeToString :: RequestMode -> String
modeToString RequestModeSameOrigin = "same-origin"
modeToString RequestModeCors = "cors"
modeToString RequestModeNoCors = "no-cors"

data RequestPriority = RequestPriorityHigh
                     | RequestPriorityLow
                     | RequestPriorityAuto

derive instance Eq RequestPriority

instance Show RequestPriority where
  show RequestPriorityHigh = "RequestPriorityHigh"
  show RequestPriorityLow = "RequestPriorityLow"
  show RequestPriorityAuto = "RequestPriorityAuto"

priorityToString :: RequestPriority -> String
priorityToString RequestPriorityHigh = "RequestPriorityHigh"
priorityToString RequestPriorityLow = "RequestPriorityLow"
priorityToString RequestPriorityAuto = "RequestPriorityAuto"

data RequestRedirect = RequestRedirectFollow
                     | RequestRedirectError
                     | RequestRedirectManual

derive instance Eq RequestRedirect

instance Show RequestRedirect where
  show RequestRedirectFollow = "RequestRedirectFollow"
  show RequestRedirectError = "RequestRedirectError"
  show RequestRedirectManual = "RequestRedirectManual"

redirectToString :: RequestRedirect -> String
redirectToString RequestRedirectFollow = "RequestRedirectFollow"
redirectToString RequestRedirectError = "RequestRedirectError"
redirectToString RequestRedirectManual = "RequestRedirectManual"

data RequestBody = RequestBodyJson Json
                 | RequestBodyForm S.URLSearchParams

instance Show RequestBody where
  show (RequestBodyJson _) = "RequestBodyJson"
  show (RequestBodyForm _) = "RequestBodyForm"

bodyToString :: RequestBody -> String
bodyToString (RequestBodyJson json) = stringify json
bodyToString (RequestBodyForm form) = show form

type RequestRecord = { body :: Maybe RequestBody
                     , cache :: Maybe RequestCache
                     , credentials :: Maybe RequestCredentials
                     , headers :: Maybe H.Headers
                     , keepalive :: Maybe Boolean
                     , method :: Maybe RequestMethod
                     , mode :: Maybe RequestMode
                     , priority :: Maybe RequestPriority
                     , redirect :: Maybe RequestRedirect
                     , referrer :: Maybe String
                     }

newtype Request = Request RequestRecord

defaultRequest :: Request
defaultRequest = Request { body: Nothing
                         , cache: Nothing
                         , credentials: Nothing
                         , headers: Nothing
                         , keepalive: Nothing
                         , method: Nothing
                         , mode: Nothing
                         , priority: Nothing
                         , redirect: Nothing
                         , referrer: Nothing
                         }

withRequest :: Request -> (RequestRecord -> RequestRecord) -> Request
withRequest (Request req) f = Request $ f req

withRequestFlip :: (RequestRecord -> RequestRecord) -> Request -> Request
withRequestFlip = flip withRequest

setCache :: RequestCache -> Request -> Request
setCache c = withRequestFlip _ { cache = Just c }

removeCache :: Request -> Request
removeCache = withRequestFlip _ { cache = Nothing }

setCredentials :: RequestCredentials -> Request -> Request
setCredentials c = withRequestFlip _ { credentials = Just c }

removeCredential :: Request -> Request
removeCredential = withRequestFlip _ { credentials = Nothing }

setHeaders :: H.Headers -> Request -> Request
setHeaders h (Request req) = Request $ req { headers = Just h}

removeHeaders :: Request -> Request
removeHeaders (Request req) = Request $ req { headers = Nothing }

setHeader :: String -> String -> Request -> Request
setHeader key value (Request req) = Request $ req { headers = h req.headers }
  where h (Just headers) = Just $ H.insert key value headers
        h Nothing = Just $ H.singleton key value

appendHeader :: String -> String -> Request -> Request
appendHeader key value (Request req) = Request $ req { headers = h req.headers }
  where h (Just headers) = Just $ H.append key value headers
        h Nothing = Just $ H.singleton key value

setKeepalive :: Boolean -> Request -> Request
setKeepalive b = withRequestFlip _ { keepalive = Just b }

removeKeepalive :: Request -> Request
removeKeepalive = withRequestFlip _ { keepalive = Nothing }

setMethod :: RequestMethod -> Request -> Request
setMethod c = withRequestFlip _ { method = Just c }

removeMethod :: Request -> Request
removeMethod = withRequestFlip _ { method = Nothing }

setMode :: RequestMode -> Request -> Request
setMode c = withRequestFlip _ { mode = Just c }

removeMode :: Request -> Request
removeMode = withRequestFlip _ { mode = Nothing }

setPriority :: RequestPriority -> Request -> Request
setPriority p = withRequestFlip _ { priority = Just p }

removePriority :: Request -> Request
removePriority = withRequestFlip _ { priority = Nothing }

setRedirect :: RequestRedirect -> Request -> Request
setRedirect c = withRequestFlip _ { redirect = Just c }

removeRedirect :: Request -> Request
removeRedirect = withRequestFlip _ { redirect = Nothing }

setReferrer :: String -> Request -> Request
setReferrer c = withRequestFlip _ { referrer = Just c }

removeReferrer :: Request -> Request
removeReferrer = withRequestFlip _ { referrer = Nothing }

setBodyJson' :: forall json. EncodeJson json => json -> Request -> Request
setBodyJson' body = withRequestFlip _ { body = Just $ RequestBodyJson $ encodeJson body }

setBodyJson :: forall json. EncodeJson json => json -> Request -> Request
setBodyJson body = setBodyJson' body <<< appendHeader "Content-Type" "application/json"

setBodyForm' :: S.URLSearchParams -> Request -> Request
setBodyForm' form = withRequestFlip _ { body = Just $ RequestBodyForm form }

setBodyForm :: S.URLSearchParams -> Request -> Request
setBodyForm form = setBodyForm' form <<< appendHeader "Content-Type" "application/x-www-form-urlencoded"

removeBody :: Request -> Request
removeBody = withRequestFlip _ { body = Nothing }

requestToInit :: Request -> F.Request
requestToInit (Request req) = F.unwrapRequestToInit req'
  where req' = F.Request { body: map bodyToString req.body
                         , cache: map cacheToString req.cache
                         , credentials: map credentialsToString req.credentials
                         , headers: req.headers
                         , keepalive: req.keepalive
                         , method: map methodToString req.method
                         , mode: map modeToString req.mode
                         , priority: map priorityToString req.priority
                         , redirect: map redirectToString req.redirect
                         , referrer: req.referrer
                         }
