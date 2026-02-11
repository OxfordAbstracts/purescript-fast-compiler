module Golem.Fetch.Response ( module Output
                            , ResponseType(..)
                            , bodyUsed
                            , headers
                            , ok
                            , redirected
                            , status
                            , responseType
                            , json
                            , text
                            ) where

import Prelude

import Data.Argonaut.Core (Json)
import Effect.Aff (Aff)
import Effect.Aff.Compat (fromEffectFnAff)
import Golem.Fetch.Unsafe.Fetch (Response) as Output
import Golem.Fetch.Unsafe.Fetch as F

data ResponseType = ResponseTypeBasic
                  | ResponseTypeCors
                  | ResponseTypeError
                  | ResponseTypeOpaque
                  | ResponseTypeOpaqueRedirect

instance Show ResponseType where
  show ResponseTypeBasic = "ResponseTypeBasic"
  show ResponseTypeCors = "ResponseTypeCors"
  show ResponseTypeError = "ResponseTypeError"
  show ResponseTypeOpaque = "ResponseTypeOpaque"
  show ResponseTypeOpaqueRedirect = "ResponseTypeOpaqueRedirect"

derive instance Eq ResponseType

typeFromString :: String -> ResponseType
typeFromString "cors" = ResponseTypeCors
typeFromString "error" = ResponseTypeError
typeFromString "opaque" = ResponseTypeOpaque
typeFromString "opaqueredirect" = ResponseTypeOpaqueRedirect
typeFromString _ = ResponseTypeBasic

bodyUsed :: F.Response -> Boolean
bodyUsed = F._response_bodyUsed

headers :: F.Response -> F.Headers
headers = F._response_headers

ok :: F.Response -> Boolean
ok = F._response_ok

redirected :: F.Response -> Boolean
redirected = F._response_redirected

status :: F.Response -> Int
status = F._response_status

responseType :: F.Response -> ResponseType
responseType = typeFromString <<< F._response_type

json :: F.Response -> Aff Json
json = fromEffectFnAff <<< F._response_json

text :: F.Response -> Aff String
text = fromEffectFnAff <<< F._response_text
