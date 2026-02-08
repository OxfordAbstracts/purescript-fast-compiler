module Grain.Router
  ( class Router
  , parse
  , useRouter
  , initialRouter
  , link
  , navigateTo
  , redirectTo
  , goForward
  , goBack
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect (Effect)
import Foreign (Foreign, unsafeToForeign)
import Grain (class GlobalGrain, GProxy, Render, VNode, useUpdater)
import Grain.Markup as H
import Web.Event.Event (EventType, preventDefault)
import Web.Event.EventTarget (addEventListener, eventListener)
import Web.HTML (window)
import Web.HTML.Event.PopStateEvent.EventTypes (popstate)
import Web.HTML.History (DocumentTitle(..), URL(..), back, forward, pushState, replaceState)
import Web.HTML.Location (pathname, search)
import Web.HTML.Window (Window, history, location, toEventTarget)

class Router a where
  parse :: String -> a

useRouter
  :: forall a
   . GlobalGrain a
  => Router a
  => GProxy a
  -> Render (Effect Unit)
useRouter proxy = do
  updateRoute <- useUpdater proxy
  pure do
    listener <- eventListener $ const do
      route <- parse <$> currentPath
      updateRoute $ const route
    window <#> toEventTarget >>= addEventListener popstate listener false

initialRouter :: forall a. Router a => Effect a
initialRouter = parse <$> currentPath

currentPath :: Effect String
currentPath = do
  l <- window >>= location
  (<>) <$> pathname l <*> search l

link :: String -> VNode
link url = H.a # H.href url # H.onClick onClick
  where
    onClick evt = preventDefault evt *> navigateTo url

navigateTo :: String -> Effect Unit
navigateTo url = do
  window >>= history >>= pushState null (DocumentTitle "") (URL url)
  window >>= dispatchEvent popstate

redirectTo :: String -> Effect Unit
redirectTo url = do
  window >>= history >>= replaceState null (DocumentTitle "") (URL url)
  window >>= dispatchEvent popstate

goForward ::Effect Unit
goForward = window >>= history >>= forward

goBack :: Effect Unit
goBack = window >>= history >>= back

null :: Foreign
null = unsafeToForeign Nothing

foreign import dispatchEvent
  :: EventType
  -> Window
  -> Effect Unit
