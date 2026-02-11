module Golem.Fetch where

import Prelude

import Effect.Aff (Aff)
import Effect.Aff.Compat (fromEffectFnAff)
import Golem.Fetch.Request (Request, requestToInit)
import Golem.Fetch.URL (class ToURL, toURL)
import Golem.Fetch.Unsafe.Fetch as F

fetch :: forall url. ToURL url => url -> Request -> Aff (F.Response)
fetch url req = fromEffectFnAff $ F._fetch_api2 (toURL url) req'
  where req' = requestToInit req

fetch' :: forall url. ToURL url => url -> Aff (F.Response)
fetch' = fromEffectFnAff <<< F._fetch_api <<< toURL
