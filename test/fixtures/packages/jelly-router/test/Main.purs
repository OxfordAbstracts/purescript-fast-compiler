module Test.Main where

import Prelude

import Data.Foldable (traverse_)
import Effect (Effect)
import Effect.Aff (launchAff_)
import Effect.Class (liftEffect)
import Jelly.Aff (awaitBody)
import Jelly.Component (class Component, text)
import Jelly.Element as JE
import Jelly.Router (class Router, mountRouter, routerLink', useCurrentRoute)
import Signal.Hooks (runHooks_, useHooks_)

main :: Effect Unit
main = launchAff_ do
  bodyMaybe <- awaitBody
  liftEffect $ runHooks_ $ traverse_ (mountRouter root) bodyMaybe

root :: forall m. Component m => Router m => m Unit
root = do
  currentRoute <- useCurrentRoute

  useHooks_ $ currentRoute <#> case _ of
    "/" -> JE.div' $ text "Home"
    "/hoge" -> JE.div' $ text "Hoge"
    "/fuga" -> JE.div' $ text "Fuga"
    "/fuga#piyo" -> JE.div' $ text "Fuga#piyo"
    _ -> JE.div' $ text "404"

  JE.div' $ routerLink' "/" $ text "Home"
  JE.div' $ routerLink' "/hoge" $ text "Hoge"
  JE.div' $ routerLink' "/fuga" $ text "Fuga"
  JE.div' $ routerLink' "/fuga#piyo" $ text "Fuga#piyo"
