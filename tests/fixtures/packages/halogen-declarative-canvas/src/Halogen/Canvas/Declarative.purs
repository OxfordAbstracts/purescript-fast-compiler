module Halogen.Canvas.Declarative
 ( declarativeCanvas
 , CanvasInput
 , DrawInstructions
 ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Traversable (for_)
import Effect (Effect)
import Effect.Class (class MonadEffect, liftEffect)
import Halogen as H
import Halogen.Component (EvalSpec)
import Halogen.HTML as HTML
import Halogen.HTML.Properties as Prop
-- import Halogen.HTML.Events as Event
import Graphics.Canvas
 ( CanvasElement
 , Context2D
 , getContext2D
 , getCanvasDimensions
 , clearRect
 )
import Unsafe.Coerce (unsafeCoerce)
import Web.HTML.HTMLElement (HTMLElement)

-- | The type of the render input given to a `declarativeCanvas` component.
-- | `width` and `height` define the dimensions of the canvas,
-- | while `draw` provides instructions for drawing its current state.
type CanvasInput =
  { width :: Int
  , height :: Int
  , draw :: DrawInstructions
  }

type State =
  { width :: Int
  , height :: Int
  }

-- | The type of `draw`. Represents instructions for drawing on the canvas.
type DrawInstructions = Context2D -> Effect Unit

type Action = DrawInstructions

refLabel :: H.RefLabel
refLabel = H.RefLabel "declCanvasRefLabel"

-- leaving queries and events as a TODO for now
-- | The declarative canvas component, which is drawn on by passing instructions in its input.
declarativeCanvas ::
  forall query output m.
  MonadEffect m =>
  H.Component query CanvasInput output m
declarativeCanvas = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval evalSpec
  }

initialState :: CanvasInput -> State
initialState { width, height } = { width, height }

render ::
  forall m.
  MonadEffect m =>
  State -> H.ComponentHTML Action () m
render rec = HTML.canvas
  [ Prop.width rec.width
  , Prop.height rec.height
  , Prop.ref refLabel
  ]

evalSpec ::
  forall output query m.
  MonadEffect m =>
  EvalSpec State query Action () CanvasInput output m
evalSpec = H.defaultEval
  { receive = handleInput
  , handleAction = handleAction
  }

handleInput :: CanvasInput -> Maybe Action
handleInput rec = Just rec.draw

handleAction ::
  forall output m.
  MonadEffect m =>
  Action ->
  H.HalogenM State Action () output m Unit
handleAction action = do
  maybeElem <- H.getHTMLElementRef refLabel
  for_ maybeElem \elem -> liftEffect do
    let c = toCanvasElement elem
    ctx <- getContext2D c
    { width, height } <- getCanvasDimensions c
    clearRect ctx { x: 0.0, y: 0.0, width, height }
    action ctx

toCanvasElement :: HTMLElement -> CanvasElement
toCanvasElement = unsafeCoerce
