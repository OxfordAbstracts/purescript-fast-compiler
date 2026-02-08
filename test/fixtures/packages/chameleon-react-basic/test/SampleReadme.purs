module Test.SampleReadme where

import Prelude

import Data.Tuple.Nested ((/\))
import Effect (Effect)
import React.Basic.DOM.Client as ReactBasicDOM
import React.Basic.Hooks as React
import Chameleon (class Html)
import Chameleon as C
import Chameleon.Impl.ReactBasic as Chameleon.React
import Web.DOM as DOM

-- Framework agnostic part

type State = Int

data Msg
  = Increment Int
  | Decrement Int

counterUpdate :: Msg -> State -> State
counterUpdate msg state = case msg of
  Increment n -> state + n
  Decrement n -> state - n

counterView :: forall html. Html html => { count :: Int } -> html Msg
counterView props =
  C.div
    [ C.style "border: 1px solid red"
    ]
    [ C.text "Counter"
    , C.div [] [ C.text $ show props.count ]
    , C.button [ C.onClick (Increment 1) ]
        [ C.text "+" ]
    , C.button [ C.onClick (Decrement 1) ]
        [ C.text "-" ]
    ]

-- React Basic Hook component

mkApp :: React.Component {}
mkApp = do
  React.component "Counter" \_props -> React.do

    state /\ setState <- React.useState 0

    let
      handler msg = setState $ counterUpdate msg

    pure
      $ Chameleon.React.runReactHtml
          { handler }
          Chameleon.React.defaultConfig
      $ counterView { count: state }

-- Mount React component

foreign import elemById :: String -> Effect DOM.Element

main :: Effect Unit
main = do
  rootElem <- elemById "root"
  app <- mkApp
  reactRoot <- ReactBasicDOM.createRoot rootElem
  ReactBasicDOM.renderRoot reactRoot (app {})