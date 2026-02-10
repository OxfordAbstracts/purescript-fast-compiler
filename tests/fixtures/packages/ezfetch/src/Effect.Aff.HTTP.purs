module Effect.Aff.HTTP (fetch, fetchWithDefaults, OptionalFields, module X) where

import Prelude

import Control.Promise (Promise)
import Control.Promise as Promise
import Data.Newtype (unwrap)
import Data.Nullable (Nullable)
import Data.Nullable as Nullable
import Data.URL (URL)
import Data.URL as URL
import Effect (Effect)
import Effect.Aff.Class (class MonadAff, liftAff)
import Foreign.Object (Object)
import Foreign.Object as Object
import Effect.Aff.HTTP.Header (Headers)
import Effect.Aff.HTTP.Header (headers) as X
import Effect.Aff.HTTP.Request (Body(..), Credentials(..), Method, RawBody, bodyHeaders, bodyToRaw)
import Effect.Aff.HTTP.Request (Method(..)) as X
import Effect.Aff.HTTP.Request as Req
import Effect.Aff.HTTP.Response (Response)
import Prim.Row (class Nub, class Union)
import Record as Record
import Type.Prelude (Proxy(..))

foreign import fetchImpl
  :: forall r
   . Record
       ( body :: Nullable RawBody
       , headers :: Object String
       , credentials :: String
       , method :: String
       , url :: String
       | r
       )
  -> Effect (Promise Response)

type OptionalFields =
  ( body :: Body
  , headers :: Headers
  , credentials :: Credentials
  )

defaults :: Record OptionalFields
defaults =
  { body: BodyEmpty
  , headers: mempty
  , credentials: SameSiteCredentials
  }

makeOptionalFields
  :: forall @x xm o
   . Nub o OptionalFields
  => Union x OptionalFields o
  => Union x xm OptionalFields
  => Record OptionalFields
  -> { | x }
  -> Record OptionalFields
makeOptionalFields d x = Record.merge x d

fetchWithDefaults
  :: forall x xm m o
   . MonadAff m
  => Nub o OptionalFields
  => Union x OptionalFields o
  => Union x xm OptionalFields
  => Record OptionalFields
  -> Method
  -> URL
  -> { | x }
  -> m Response
fetchWithDefaults defaults' method url x =
  let
    methodStr = case method of
      Req.GET -> "GET"
      Req.PUT -> "PUT"
      Req.POST -> "POST"
      Req.PATCH -> "PATCH"
      Req.DELETE -> "DELETE"
      Req.HEAD -> "HEAD"

    credsStr = case _ of
      SameSiteCredentials -> "same-origin"
      OmitCredentials -> "omit"
      IncludeCredentials -> "include"

    fields =
      Record.modify (Proxy @"credentials") credsStr
        $ Record.modify (Proxy @"headers") (Object.fromFoldableWithIndex <<< unwrap)
        $ Record.insert (Proxy @"method") methodStr
        $ Record.insert (Proxy @"url") (URL.toString url)
        $ makeOptionalFields @x defaults' x
  in
    do
      bodyHeaders' <- (Object.fromFoldableWithIndex <<< unwrap) <$> bodyHeaders fields.body
      bodyRaw <- Nullable.toNullable <$> bodyToRaw fields.body
      let
        fields' =
          Record.modify (Proxy @"headers") (Object.union bodyHeaders')
            $ Record.set (Proxy @"body") bodyRaw
            $ fields

      liftAff $ Promise.toAffE $ fetchImpl fields'

fetch
  :: forall x xm m o
   . MonadAff m
  => Nub o OptionalFields
  => Union x OptionalFields o
  => Union x xm OptionalFields
  => Method
  -> URL
  -> { | x }
  -> m Response
fetch = fetchWithDefaults defaults
