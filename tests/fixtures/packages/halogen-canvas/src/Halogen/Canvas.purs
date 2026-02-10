module Halogen.Canvas
  ( Dimensions(..)
  , component
  ) where

import Prelude

import Control.Monad.Reader (runReaderT)
import Control.Monad.Rec.Class (class MonadRec)
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse, traverse_)
import Effect.Aff.Class (class MonadAff)
import Graphics.Canvas (getContext2D)
import Graphics.Canvas.Free (CanvasContext, CanvasT, runCanvasT)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Unsafe.Coerce (unsafeCoerce)

type Dimensions =
  { width :: Int
  , height :: Int
  }

type State =
  { dimensions :: Dimensions
  , canvas :: Maybe CanvasContext
  }

data Action = Initialize

component :: forall o m. MonadAff m => MonadRec m => H.Component (CanvasT m) Dimensions o m
component = do
  H.mkComponent
    { initialState: \dimensions -> { dimensions, canvas: Nothing }
    , render
    , eval: H.mkEval $ H.defaultEval { handleAction = handleAction
                                     , handleQuery = handleQuery 
                                     , initialize = Just Initialize
                                     }
    }

render :: forall m. State -> H.ComponentHTML Action () m
render { dimensions } =
  HH.canvas
    [ HP.ref (H.RefLabel "canvas")
    , HP.width dimensions.width
    , HP.height dimensions.height
    ]

handleAction :: forall m o .
                MonadAff m
             => Action
             -> H.HalogenM State Action () o m Unit
handleAction = case _ of
  Initialize -> do
    e <- H.getRef (H.RefLabel "canvas")
    flip traverse_ e $ \ce -> do
       let canvasElement = unsafeCoerce ce
       context2D <- H.liftEffect $ getContext2D canvasElement
       H.modify_ (\st -> st { canvas = Just { canvasElement, context2D } })


handleQuery :: forall m o a .
                MonadAff m
             => MonadRec m 
             => CanvasT m a
             -> H.HalogenM State Action () o m (Maybe a)
handleQuery f = do 
  { canvas } <- H.get
  flip traverse canvas $ \c -> do
    H.lift $ runReaderT (runCanvasT f) c

