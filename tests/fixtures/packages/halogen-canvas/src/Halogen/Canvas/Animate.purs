module Halogen.Canvas.Animate
  ( Animation(..)
  , component
  ) where

import Prelude

import Control.Monad.Rec.Class (class MonadRec)
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Graphics.Canvas.Free (CanvasT, clearRect, getHeight, getWidth, withContext)
import Halogen as H
import Halogen.Canvas (Dimensions)
import Halogen.Canvas as Canvas
import Halogen.HTML as HH
import Halogen.Subscription as HS
import Type.Proxy (Proxy(..))
import Web.HTML (window)
import Web.HTML.Window.AnimationFrame (DOMHighResTimestamp, requestAnimationFrame)

type Animation m =
  { dimensions :: Dimensions
  , animation :: DOMHighResTimestamp -> CanvasT m Unit
  }

type State m =
  { dimensions :: Dimensions
  , animation :: DOMHighResTimestamp -> CanvasT m Unit
  }

type Slots m = ( canvas :: forall o. H.Slot (CanvasT m) o Unit ) 

_canvas = Proxy :: Proxy "canvas"

data Action =
    Initialize
  | AnimationFrame DOMHighResTimestamp

component :: forall q o m. MonadAff m => MonadRec m => H.Component q (Animation m) o m
component = do
  H.mkComponent
    { initialState: \{ dimensions, animation } -> { dimensions, animation }
    , render
    , eval: H.mkEval $ H.defaultEval { handleAction = handleAction
                                     , initialize = Just Initialize
                                     }
    }

render :: forall m. MonadAff m => MonadRec m => State m -> H.ComponentHTML Action (Slots m) m
render { dimensions } = HH.slot_ _canvas unit Canvas.component dimensions


handleAction :: forall m o .
                MonadAff m
             => MonadRec m
             => Action
             -> H.HalogenM (State m) Action (Slots m) o m Unit
handleAction = case _ of
  Initialize -> do
    { emitter, listener } <- H.liftEffect HS.create
    let animationLoop t = do
          HS.notify listener t
          void $ window >>= requestAnimationFrame animationLoop
    H.liftEffect $ void $ window >>= requestAnimationFrame animationLoop
    void $ H.subscribe (AnimationFrame <$> emitter)
  AnimationFrame t -> do
    { animation } <- H.get
    let draw = withContext do
          width <- getWidth
          height <- getHeight
          clearRect { x: 0.0, y: 0.0, width, height }
          animation t
    void $ H.query _canvas unit draw



