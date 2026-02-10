module Test.SampleReadme where

import Prelude

import Effect (Effect)
import Effect.Aff (launchAff_)
import Halogen (liftEffect)
import Halogen as Halogen
import Halogen.VDom.Driver as HalogenVDOM
import Chameleon (class Html)
import Chameleon as C
import Chameleon.Impl.Halogen as Chameleon.Halogen
import Web.HTML (HTMLElement)

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

-- Halogen component

app :: forall q i o m. Halogen.Component q i o m
app =
  Halogen.mkComponent
    { initialState
    , render
    , eval: Halogen.mkEval $ Halogen.defaultEval { handleAction = handleAction }
    }
  where
  initialState _ = 0

  render state =
    Chameleon.Halogen.runHalogenHtml $ counterView { count: state }

  handleAction msg = Halogen.modify_ $ counterUpdate msg

-- Mount Halogen component

foreign import elemById :: String -> Effect HTMLElement

main :: Effect Unit
main = launchAff_ do
  rootElem <- liftEffect $ elemById "root"
  _ <- HalogenVDOM.runUI app unit rootElem
  pure unit