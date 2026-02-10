module Chameleon.Impl.Halogen.Mount.Routed
  ( RouteIO
  , RouteSpec
  , mkRoutableComponent
  )
  where

import Prelude

import Data.Maybe (Maybe(..))
import Data.These (These(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Halogen (ComponentSlot, HalogenM, get, liftEffect, subscribe)
import Halogen as H
import Halogen as Halogen
import Halogen.HTML (HTML)
import Halogen.Subscription (makeEmitter)

import Chameleon.Impl.Halogen (HalogenHtml)
import Chameleon.Impl.Halogen as VDOM.Halogen

type UI html msg sta =
  { view :: sta -> html msg
  , update :: msg -> sta -> sta
  , init :: sta
  }

data Msg route msg = Init | ChildMsg msg | MsgNewRoute route

type RouteSpec route msg sta =
  { updateStateFromRoute :: route -> sta -> sta
  , mkRoute :: msg -> sta -> These route msg
  }

type RouteIO route =
  { pushRoute :: route -> Effect Unit
  , listen :: (route -> Effect Unit) -> Effect (Effect Unit)
  }

mkRoutableComponent
  :: forall q i o msg sta route
   . { routeIO :: RouteIO route
     , routeSpec :: RouteSpec route msg sta
     , onStateChange :: sta -> sta -> Effect Unit
     }
  -> UI HalogenHtml msg sta
  -> (Halogen.Component q i o Aff)
mkRoutableComponent { routeSpec, routeIO, onStateChange } ui =
  H.mkComponent
    { initialState
    , render
    , eval: H.mkEval $ H.defaultEval
        { handleAction = handleAction
        , initialize = Just Init
        }
    }

  where
  initialState :: i -> sta
  initialState _ = ui.init

  render :: sta -> HTML (ComponentSlot () Aff (Msg route msg)) (Msg route msg)
  render state = VDOM.Halogen.runHalogenHtml $ ChildMsg <$> ui.view state

  handleAction :: Msg route msg -> HalogenM sta (Msg route msg) () o Aff Unit
  handleAction msg_ = do
    oldState <- get

    case msg_ of
      Init -> do
        _ <- subscribe (map MsgNewRoute $ makeEmitter routeIO.listen)
        pure unit

      MsgNewRoute route -> do
        H.modify_ $ routeSpec.updateStateFromRoute route

      ChildMsg msg -> do
        state <- get
        case routeSpec.mkRoute msg state of
          This route -> do
            liftEffect $ routeIO.pushRoute route

          That msg' -> do
            H.modify_ $ ui.update msg'

          Both route msg' -> do
            liftEffect $ routeIO.pushRoute route
            H.modify_ $ ui.update msg'

    newState <- get
    liftEffect $ onStateChange oldState newState
