-- | This module defines functions for working with the HTML5 Canvas in a
-- | `MonadCanvasAction` (e.g. `CanvasAction`). This is to make canvas actions
-- | composable without having to worry about passing a `Context2D` argument to
-- | every function.
module Graphics.CanvasAction
  ( createCanvas
  , createCanvas'
  , getCanvasElementById
  , querySelectCanvas
  , getContext2D
  , getContext2DById
  , querySelectContext2D

  , runActionOffscreen
  , runActionOffscreen'
  , asEffect
  , launchCanvasAff
  , launchCanvasAff_

  , withFull
  , withMidPos

  , getCanvas
  , getCtx

  , fillRect
  , fillRectFull
  , strokeRect
  , strokeRectFull
  , clearRect
  , clearRectFull

  , CanvasStyleRep
  , styleIsString
  , styleIsGradient
  , styleIsPattern
  , styleToString
  , styleToGradient
  , styleToPattern
  , class CanvasStyle
  , toStyleRep
  , class CanvasColor
  , toColorRep
  , toStyleRepDefault

  , setFillStyle
  , setStrokeStyle
  , getFillStyle
  , getStrokeStyle
  , filled
  , stroked

  , setLineWidth
  , setLineDash
  , setShadowBlur
  , setShadowOffsetX
  , setShadowOffsetY
  , setShadowOffset
  , setShadowColor
  , setMiterLimit
  , setLineCap
  , setLineJoin
  , setGlobalCompositeOperation
  , setGlobalAlpha

  , getTextAlign
  , setTextAlign
  , getTextBaseline
  , setTextBaseline
  , getFont
  , setFont
  , fillText
  , strokeText
  , measureText

  , getDimensions
  , setDimensions
  , getHeight
  , setHeight
  , getWidth
  , setWidth
  , toDataUrl

  , getImageData
  , putImageDataFull
  , putImageData
  , createImageData
  , createImageDataCopy

  , imageSource
  , drawImage
  , drawImageScale
  , drawImageFull
  , tryLoadImage
  , tryLoadImage'
  , loadImageAff
  , setImageSmoothing
  , getImageSmoothing

  , createPattern

  , linearGradient
  , radialGradient
  , createLinearGradient
  , createRadialGradient
  , addColorStop

  , save
  , restore
  , restoreAfter

  , module Exports
  ) where

import Prelude

import Color (Color, cssStringRGBA)
import Control.Monad.Reader (ReaderT(..), ask)
import Data.Either (Either(..))
import Data.Foldable (class Foldable, for_)
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Data.Vector.Polymorphic (Rect(..), Vector2, convertRegion, midPos, (><))
import Data.Vector.Polymorphic.Class (class ToPos, class ToRegion, class ToSize, toPos, toRegion, toSize)
import Effect (Effect)
import Effect.Aff (Fiber, effectCanceler, launchAff, makeAff)
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (liftEffect, class MonadEffect)
import Effect.Exception (error)
import Effect.Ref as Ref
import Graphics.Canvas (CanvasElement, CanvasGradient, CanvasImageSource, CanvasPattern, Composite, Context2D, Dimensions, ImageData, LineCap, LineJoin, LinearGradient, PatternRepeat, RadialGradient, Rectangle, TextAlign, TextBaseline, TextMetrics)
import Graphics.Canvas (CanvasGradient, CanvasImageSource, CanvasPattern, Composite(..), Context2D, Dimensions, ImageData, LineCap(..), LineJoin(..), LinearGradient, PatternRepeat(..), RadialGradient, TextAlign(..), TextBaseline(..), TextMetrics, imageDataBuffer, imageDataHeight, imageDataWidth) as Exports
import Graphics.Canvas as C
import Graphics.CanvasAction.Class (class MonadCanvasAction, liftCanvasAction)
import Graphics.CanvasAction.Class (class MonadCanvasAction, liftCanvasAction, class MonadCanvasAff, liftCanvasAff) as Exports
import Graphics.CanvasAction.Types (CanvasAction, runAction, CanvasAff, runCanvasAff)
import Graphics.CanvasAction.Types (CanvasAction, runAction, CanvasAff, runCanvasAff) as Exports
import Unsafe.Coerce (unsafeCoerce)
import Web.DOM (Element)
import Web.DOM.Document (Document, createElement)
import Web.DOM.ParentNode (QuerySelector(..)) as Exports
import Web.DOM.ParentNode (QuerySelector, querySelector)
import Web.HTML (window)
import Web.HTML.HTMLCanvasElement (fromElement, HTMLCanvasElement)
import Web.HTML.HTMLDocument (toDocument, toParentNode) as HTMLDocument
import Web.HTML.Window (document)

createCanvas_ ∷ Document → Effect HTMLCanvasElement
createCanvas_ = createElement "canvas" >>> map unsafeCoerceElem
  where
  unsafeCoerceElem ∷ Element → HTMLCanvasElement
  unsafeCoerceElem = unsafeCoerce

coerceHTMLCanvas ∷ HTMLCanvasElement → CanvasElement
coerceHTMLCanvas = unsafeCoerce

coerceCanvas ∷ CanvasElement → HTMLCanvasElement
coerceCanvas = unsafeCoerce

-- | Same as `createCanvas`, but allows for specifying the `Document` object to
-- | create the canvas with
createCanvas'
  ∷ ∀ m s
  . MonadEffect m
  ⇒ ToSize Number s
  ⇒ Document
  → s
  → m HTMLCanvasElement
createCanvas' doc size = liftEffect do
  let (width >< height) = toSize size
  canvas ← createCanvas_ doc
  C.setCanvasDimensions (coerceHTMLCanvas canvas) { width, height }
  pure canvas

-- | Create an `HTMLCanvasElement` of the given size in any `MonadEffect`
createCanvas ∷ ∀ m s. MonadEffect m ⇒ ToSize Number s ⇒ s → m HTMLCanvasElement
createCanvas s = do
  doc ← liftEffect (window >>= document)
  createCanvas' (HTMLDocument.toDocument doc) s

getCanvasElementById ∷ ∀ m. MonadEffect m ⇒ String → m (Maybe HTMLCanvasElement)
getCanvasElementById id = (map <<< map) coerceCanvas $
  liftEffect (C.getCanvasElementById id)

querySelectCanvas
  ∷ ∀ m. MonadEffect m ⇒ QuerySelector → m (Maybe HTMLCanvasElement)
querySelectCanvas canvas = liftEffect do
  doc ← window >>= document <#> HTMLDocument.toParentNode
  querySelector canvas doc <#> (=<<) fromElement

getContext2D ∷ ∀ m. MonadEffect m ⇒ HTMLCanvasElement → m Context2D
getContext2D = liftEffect <<< C.getContext2D <<< coerceHTMLCanvas

getContext2DById ∷ ∀ m. MonadEffect m ⇒ String → m (Maybe Context2D)
getContext2DById = getCanvasElementById >=> traverse getContext2D

querySelectContext2D ∷ ∀ m. MonadEffect m ⇒ QuerySelector → m (Maybe Context2D)
querySelectContext2D = querySelectCanvas >=> traverse getContext2D

{-
| Run a `CanvasAction` in a `MonadEffect`, on a created canvas with the
| provided size. This can be useful for creating patterns for use as a
| fillStyle or strokeStyle.
|
| For example:
|
| ```purescript
| action ∷ ∀ m. MonadCanvasAction m ⇒ m Unit
| action = do
|   pattern ← runActionOffscreen (20.0 >< 20.0) do
|     filled "#aaf" fillRectFull
|     filled "#afa" $ fillRect (makeRect 0.0 10.0 10.0 10.0)
|     filled "#faa" $ fillRect (makeRect 10.0 0.0 10.0 10.0)
|     imageSource >>= (_ `createPattern` Repeat)
|   (fillWith pattern Nonzero <=< runPath) do
|     circle (200.0 >< 200.0) 175.0
|     circle ( 50.0 ><  50.0)  50.0
|     circle ( 50.0 >< 350.0)  50.0
|     circle (350.0 ><  50.0)  50.0
|     circle (350.0 >< 350.0)  50.0
| ```
-}
runActionOffscreen
  ∷ ∀ m a s
  . MonadEffect m
  ⇒ ToSize Number s
  ⇒ s
  → CanvasAction a
  → m a
runActionOffscreen size action = do
  ctx ← createCanvas size >>= getContext2D
  runAction ctx action

-- | Run a `CanvasAction` in a `MonadCanvasAction`, on a created canvas with
-- | the same size as the "main" canvas. This can be useful for creating
-- | patterns for use as a fillStyle or strokeStyle. See `runActionOffscreen`
-- | for an example.
runActionOffscreen' ∷ ∀ m a. MonadCanvasAction m ⇒ CanvasAction a → m a
runActionOffscreen' action = do
  size ← getDimensions
  runActionOffscreen size action

-- | Runs a `CanvasAction` in a `MonadEffect` inside a functor context. Useful
-- | for turning a function that returns a `CanvasAction` into a function that
-- | returns an `Effect`.
asEffect
  ∷ ∀ m f a
  . Functor f
  ⇒ MonadEffect m
  ⇒ Context2D
  → f (CanvasAction a)
  → f (m a)
asEffect ctx = map (runAction ctx)

launchCanvasAff ∷ ∀ a. Context2D → CanvasAff a → Effect (Fiber a)
launchCanvasAff ctx aff = launchAff (runCanvasAff ctx aff)

launchCanvasAff_ ∷ ∀ a. Context2D → CanvasAff a → Effect Unit
launchCanvasAff_ ctx aff = void (launchCanvasAff ctx aff)

withCtx ∷ ∀ m a. MonadCanvasAction m ⇒ (Context2D → Effect a) → m a
withCtx = liftCanvasAction <<< ReaderT

withCtx1
  ∷ ∀ m a b. MonadCanvasAction m ⇒ (Context2D → a → Effect b) → (a → m b)
withCtx1 action a = withCtx \ctx → action ctx a

withCtx2
  ∷ ∀ m a b c
  . MonadCanvasAction m
  ⇒ (Context2D → a → b → Effect c)
  → (a → b → m c)
withCtx2 action a b = withCtx \ctx → action ctx a b

withCtx3
  ∷ ∀ m a b c d
  . MonadCanvasAction m
  ⇒ (Context2D → a → b → c → Effect d)
  → (a → b → c → m d)
withCtx3 action a b c = withCtx \ctx → action ctx a b c

withCtx4
  ∷ ∀ m a b c d e
  . MonadCanvasAction m
  ⇒ (Context2D → a → b → c → d → Effect e)
  → (a → b → c → d → m e)
withCtx4 action a b c d = withCtx \ctx → action ctx a b c d

withCtx5
  ∷ ∀ m a b c d e f
  . MonadCanvasAction m
  ⇒ (Context2D → a → b → c → d → e → Effect f)
  → (a → b → c → d → e → m f)
withCtx5 action a b c d e = withCtx \ctx → action ctx a b c d e

withCtx7
  ∷ ∀ m a b c d e f g h
  . MonadCanvasAction m
  ⇒ (Context2D → a → b → c → d → e → f → g → Effect h)
  → (a → b → c → d → e → f → g → m h)
withCtx7 action a b c d e f g = withCtx \ctx → action ctx a b c d e f g

withCtx9
  ∷ ∀ m a b c d e f g h i j
  . MonadCanvasAction m
  ⇒ (Context2D → a → b → c → d → e → f → g → h → i → Effect j)
  → (a → b → c → d → e → f → g → h → i → m j)
withCtx9 action a b c d e f g h i = withCtx \ctx → action ctx a b c d e f g h i

-- | From a function taking some region and returning a `MonadCanvasAction`,
-- | make a `MonadCanvasAction` that calls the original function with the whole
-- | canvas as the region. This can for example be used to draw an image scaled
-- | to fill the entire canvas: `withFull \r → drawImageScale r image`
withFull ∷ ∀ m a. MonadCanvasAction m ⇒ (Rect Number → m a) → m a
withFull action = getDimensions >>= (toSize >>> toRegion >>> action)

-- | From a function taking some position and returning a `MonadCanvasAction`,
-- | make a `MonadCanvasAction` that calls the original function with the center
-- | of the canvas as a position.
withMidPos
  ∷ ∀ m a
  . MonadCanvasAction m
  ⇒ (Vector2 Number → m a)
  → m a
withMidPos action = getDimensions >>= (toSize >>> midPos >>> action)

-- | Get the canvas of a `Context2D`
foreign import getCanvasEffect ∷ Context2D → Effect HTMLCanvasElement

-- | Get the canvas in a `MonadCanvasAction`
getCanvas ∷ ∀ m. MonadCanvasAction m ⇒ m HTMLCanvasElement
getCanvas = withCtx getCanvasEffect

-- | Get the canvas rendering context in a `MonadCanvasAction`
getCtx ∷ ∀ m. MonadCanvasAction m ⇒ m Context2D
getCtx = withCtx pure

withCanvas ∷ ∀ m a. MonadCanvasAction m ⇒ (CanvasElement → Effect a) → m a
withCanvas action = withCtx \ctx →
  getCanvasEffect ctx <#> coerceHTMLCanvas >>= action

withCanvas1
  ∷ ∀ m a b. MonadCanvasAction m ⇒ (CanvasElement → a → Effect b) → (a → m b)
withCanvas1 action a = withCanvas \canv → action canv a

-- | Fill a rectangular area
fillRect ∷ ∀ m r. MonadCanvasAction m ⇒ ToRegion Number r ⇒ r → m Unit
fillRect = withCtx1 C.fillRect <<< convertRegion

-- | Fill a rectangular area that covers the entire canvas
fillRectFull ∷ ∀ m. MonadCanvasAction m ⇒ m Unit
fillRectFull = withFull fillRect

-- | Stroke a rectangular area
strokeRect ∷ ∀ m r. MonadCanvasAction m ⇒ ToRegion Number r ⇒ r → m Unit
strokeRect = withCtx1 C.strokeRect <<< convertRegion

-- | Stroke a rectangular area that covers the entire canvas
strokeRectFull ∷ ∀ m. MonadCanvasAction m ⇒ m Unit
strokeRectFull = withFull strokeRect

-- | Clear a rectangular area
clearRect ∷ ∀ m r. MonadCanvasAction m ⇒ ToRegion Number r ⇒ r → m Unit
clearRect = withCtx1 C.clearRect <<< convertRegion

-- | Clear a rectangular area that covers the entire canvas
clearRectFull ∷ ∀ m. MonadCanvasAction m ⇒ m Unit
clearRectFull = withFull clearRect

-- | A value that can be passed to `setFillStyle` and similar functions.
-- | Runtime representation should be either a `String`, a `CanvasGradient` or
-- | a `CanvasPattern`.
foreign import data CanvasStyleRep ∷ Type

foreign import styleIsString ∷ CanvasStyleRep → Boolean

foreign import styleIsGradient ∷ CanvasStyleRep → Boolean

foreign import styleIsPattern ∷ CanvasStyleRep → Boolean

unsafeStyleToX ∷ ∀ a. (CanvasStyleRep → Boolean) → (CanvasStyleRep → Maybe a)
unsafeStyleToX isCorrect style
  | isCorrect style = Just (unsafeCoerce style)
  | otherwise = Nothing

styleToString ∷ CanvasStyleRep → Maybe String
styleToString = unsafeStyleToX styleIsString

styleToGradient ∷ CanvasStyleRep → Maybe CanvasGradient
styleToGradient = unsafeStyleToX styleIsGradient

styleToPattern ∷ CanvasStyleRep → Maybe CanvasPattern
styleToPattern = unsafeStyleToX styleIsPattern

-- | Class describing types that can be turned into a valid `CanvasStyleRep`
class CanvasStyle style where
  toStyleRep ∷ style → CanvasStyleRep

instance CanvasStyle CanvasStyleRep where
  toStyleRep = identity

instance CanvasStyle CanvasGradient where
  toStyleRep = (unsafeCoerce ∷ CanvasGradient → CanvasStyleRep)

instance CanvasStyle CanvasPattern where
  toStyleRep = (unsafeCoerce ∷ CanvasPattern → CanvasStyleRep)

instance CanvasStyle String where
  toStyleRep = toStyleRepDefault

instance CanvasStyle Color where
  toStyleRep = toStyleRepDefault

-- | Class describing types that can be turned into a string representing a
-- | canvas color.
class CanvasStyle color ⇐ CanvasColor color where
  toColorRep ∷ color → String

instance CanvasColor String where
  toColorRep = identity

instance CanvasColor Color where
  toColorRep = cssStringRGBA

-- | A default implementation of `toStyleRep` using `toColorRep`.
toStyleRepDefault ∷ ∀ color. CanvasColor color ⇒ color → CanvasStyleRep
toStyleRepDefault = toColorRep >>> (unsafeCoerce ∷ String → CanvasStyleRep)

foreign import setFillStyleImpl ∷ Context2D → CanvasStyleRep → Effect Unit

setFillStyle ∷ ∀ m r. MonadCanvasAction m ⇒ CanvasStyle r ⇒ r → m Unit
setFillStyle = withCtx1 setFillStyleImpl <<< toStyleRep

foreign import setStrokeStyleImpl ∷ Context2D → CanvasStyleRep → Effect Unit

setStrokeStyle ∷ ∀ m r. MonadCanvasAction m ⇒ CanvasStyle r ⇒ r → m Unit
setStrokeStyle = withCtx1 setStrokeStyleImpl <<< toStyleRep

foreign import getFillStyleImpl ∷ Context2D → Effect CanvasStyleRep

getFillStyle ∷ ∀ m. MonadCanvasAction m ⇒ m CanvasStyleRep
getFillStyle = withCtx getFillStyleImpl

foreign import getStrokeStyleImpl ∷ Context2D → Effect CanvasStyleRep

getStrokeStyle ∷ ∀ m. MonadCanvasAction m ⇒ m CanvasStyleRep
getStrokeStyle = withCtx getStrokeStyleImpl

-- | Run a `MonadCanvasAction` with the given fillStyle, resetting it to the
-- | previous value after
filled
  ∷ ∀ m a style. MonadCanvasAction m ⇒ CanvasStyle style ⇒ style → m a → m a
filled style action = do
  old ← getFillStyle
  setFillStyle style *> action <* setFillStyle old

-- | Run a `MonadCanvasAction` with the given strokeStyle, resetting it to the
-- | previous value after
stroked
  ∷ ∀ m a style. MonadCanvasAction m ⇒ CanvasStyle style ⇒ style → m a → m a
stroked style action = do
  old ← getStrokeStyle
  setStrokeStyle style *> action <* setStrokeStyle old

setLineWidth ∷ ∀ m. MonadCanvasAction m ⇒ Number → m Unit
setLineWidth = withCtx1 C.setLineWidth

setLineDash ∷ ∀ m. MonadCanvasAction m ⇒ Array Number → m Unit
setLineDash = withCtx1 C.setLineDash

setShadowBlur ∷ ∀ m. MonadCanvasAction m ⇒ Number → m Unit
setShadowBlur = withCtx1 C.setShadowBlur

setShadowOffsetX ∷ ∀ m. MonadCanvasAction m ⇒ Number → m Unit
setShadowOffsetX = withCtx1 C.setShadowOffsetX

setShadowOffsetY ∷ ∀ m. MonadCanvasAction m ⇒ Number → m Unit
setShadowOffsetY = withCtx1 C.setShadowOffsetY

-- | Set x and y shadow offset at the same time
setShadowOffset ∷ ∀ m p. MonadCanvasAction m ⇒ ToPos Number p ⇒ p → m Unit
setShadowOffset offset = setShadowOffsetX x *> setShadowOffsetY y
  where
  (x >< y) = toPos offset

setShadowColor
  ∷ ∀ m color. MonadCanvasAction m ⇒ CanvasColor color ⇒ color → m Unit
setShadowColor = withCtx1 C.setShadowColor <<< toColorRep

setMiterLimit ∷ ∀ m. MonadCanvasAction m ⇒ Number → m Unit
setMiterLimit = withCtx1 C.setMiterLimit

setLineCap ∷ ∀ m. MonadCanvasAction m ⇒ LineCap → m Unit
setLineCap = withCtx1 C.setLineCap

setLineJoin ∷ ∀ m. MonadCanvasAction m ⇒ LineJoin → m Unit
setLineJoin = withCtx1 C.setLineJoin

setGlobalCompositeOperation ∷ ∀ m. MonadCanvasAction m ⇒ Composite → m Unit
setGlobalCompositeOperation = withCtx1 C.setGlobalCompositeOperation

setGlobalAlpha ∷ ∀ m. MonadCanvasAction m ⇒ Number → m Unit
setGlobalAlpha = withCtx1 C.setGlobalAlpha

getTextAlign ∷ ∀ m. MonadCanvasAction m ⇒ m TextAlign
getTextAlign = withCtx C.textAlign

setTextAlign ∷ ∀ m. MonadCanvasAction m ⇒ TextAlign → m Unit
setTextAlign = withCtx1 C.setTextAlign

getTextBaseline ∷ ∀ m. MonadCanvasAction m ⇒ m TextBaseline
getTextBaseline = withCtx C.textBaseline

setTextBaseline ∷ ∀ m. MonadCanvasAction m ⇒ TextBaseline → m Unit
setTextBaseline = withCtx1 C.setTextBaseline

getFont ∷ ∀ m. MonadCanvasAction m ⇒ m String
getFont = withCtx C.font

setFont ∷ ∀ m. MonadCanvasAction m ⇒ String → m Unit
setFont = withCtx1 C.setFont

fillText ∷ ∀ m p. MonadCanvasAction m ⇒ ToPos Number p ⇒ String → p → m Unit
fillText text pos = withCtx3 C.fillText text x y
  where
  (x >< y) = toPos pos

strokeText ∷ ∀ m p. MonadCanvasAction m ⇒ ToPos Number p ⇒ String → p → m Unit
strokeText text pos = withCtx3 C.strokeText text x y
  where
  (x >< y) = toPos pos

measureText ∷ ∀ m. MonadCanvasAction m ⇒ String → m TextMetrics
measureText = withCtx1 C.measureText

getDimensions ∷ ∀ m. MonadCanvasAction m ⇒ m Dimensions
getDimensions = withCanvas C.getCanvasDimensions

setDimensions ∷ ∀ m. MonadCanvasAction m ⇒ Dimensions → m Unit
setDimensions = withCanvas1 C.setCanvasDimensions

getHeight ∷ ∀ m. MonadCanvasAction m ⇒ m Number
getHeight = withCanvas C.getCanvasHeight

setHeight ∷ ∀ m. MonadCanvasAction m ⇒ Number → m Unit
setHeight = withCanvas1 C.setCanvasHeight

getWidth ∷ ∀ m. MonadCanvasAction m ⇒ m Number
getWidth = withCanvas C.getCanvasWidth

setWidth ∷ ∀ m. MonadCanvasAction m ⇒ Number → m Unit
setWidth = withCanvas1 C.setCanvasWidth

-- | Create a data URL for the current canvas contents
toDataUrl ∷ ∀ m. MonadCanvasAction m ⇒ m String
toDataUrl = withCanvas C.canvasToDataURL

getImageData ∷ ∀ m r. MonadCanvasAction m ⇒ ToRegion Number r ⇒ r → m ImageData
getImageData region = withCtx4 C.getImageData x y width height
  where
  { x, y, width, height } = convertRegion region ∷ Rectangle

-- | Render image data on the canvas. The first argument (`p`) is the point on
-- | the canvas to place the topleft of the data. The second argument (`r`) is
-- | the region of the `ImageData` to render.
putImageDataFull
  ∷ ∀ m p r
  . MonadCanvasAction m
  ⇒ ToPos Number p
  ⇒ ToRegion Number r
  ⇒ p
  → r
  → ImageData
  → m Unit
putImageDataFull dest dirty img =
  withCtx7 C.putImageDataFull img x y dx dy dw dh
  where
  (x >< y) = toPos dest
  (Rect (dx >< dy) (dw >< dh)) = toRegion dirty

-- | Render image data on the canvas. The first argument (`p`) is the point on
-- | the canvas to place the topleft of the data.
putImageData
  ∷ ∀ m p
  . MonadCanvasAction m
  ⇒ ToPos Number p
  ⇒ p
  → ImageData
  → m Unit
putImageData dest img = withCtx3 C.putImageData img x y
  where
  (x >< y) = toPos dest

createImageData ∷ ∀ m s. MonadCanvasAction m ⇒ ToSize Number s ⇒ s → m ImageData
createImageData size = withCtx2 C.createImageData w h
  where
  (w >< h) = toSize size

createImageDataCopy ∷ ∀ m. MonadCanvasAction m ⇒ ImageData → m ImageData
createImageDataCopy = withCtx1 C.createImageDataCopy

imageSource ∷ ∀ m. MonadCanvasAction m ⇒ m CanvasImageSource
imageSource = withCanvas $ pure <<< C.canvasElementToImageSource

drawImage
  ∷ ∀ m p. MonadCanvasAction m ⇒ ToPos Number p ⇒ p → CanvasImageSource → m Unit
drawImage pos img = withCtx3 C.drawImage img x y
  where
  (x >< y) = toPos pos

-- | Draw an image, scaled to fit the provided region
drawImageScale
  ∷ ∀ m r
  . MonadCanvasAction m
  ⇒ ToRegion Number r
  ⇒ r
  → CanvasImageSource
  → m Unit
drawImageScale dirty img = withCtx5 C.drawImageScale img x y w h
  where
  (Rect (x >< y) (w >< h)) = toRegion dirty

-- | Draw an image on the canvas. The first arugment is the region of the source
-- | image to draw, and the second argument is the region on the canvas to draw
-- | it in.
drawImageFull
  ∷ ∀ m r
  . MonadCanvasAction m
  ⇒ ToRegion Number r
  ⇒ r
  → r
  → CanvasImageSource
  → m Unit
drawImageFull source dirty img =
  withCtx9 C.drawImageFull img sx sy sw sh dx dy dw dh
  where
  (Rect (sx >< sy) (sw >< sh)) = toRegion source
  (Rect (dx >< dy) (dw >< dh)) = toRegion dirty

-- | Asynchronously load an image file by specifying its path and a callback
-- | `Effect Unit`.
tryLoadImage'
  ∷ ∀ m
  . MonadEffect m
  ⇒ String
  → (Maybe CanvasImageSource → Effect Unit)
  → m Unit
tryLoadImage' path action = liftEffect $ C.tryLoadImage path action

-- | Asynchronously load an image file by specifying its path and a callback
-- | `CanvasAction Unit`.
tryLoadImage
  ∷ ∀ m
  . MonadCanvasAction m
  ⇒ String
  → (Maybe CanvasImageSource → CanvasAction Unit)
  → m Unit
tryLoadImage path action = do
  ctx ← liftCanvasAction ask
  tryLoadImage' path (runAction ctx <<< action)

-- | Asynchrounously load an image file by specifying its path. The returned
-- | `MonadAff` will throw an error if the image wasn't found.
loadImageAff ∷ ∀ m. MonadAff m ⇒ String → m CanvasImageSource
loadImageAff path = liftAff $ makeAff \cb → do
  canceled ← Ref.new false
  tryLoadImage' path do
    unlessM (Ref.read canceled) <<< case _ of
      Just image → cb (Right image)
      Nothing → cb (Left do error ("Image \"" <> path <> "\" not found"))
  pure do effectCanceler (Ref.write true canceled)

foreign import setImageSmoothingImpl ∷ Context2D → Boolean → Effect Unit

-- | Set the context's `imageSmoothingEnabled` property
setImageSmoothing ∷ ∀ m. MonadCanvasAction m ⇒ Boolean → m Unit
setImageSmoothing = withCtx1 setImageSmoothingImpl

foreign import getImageSmoothingImpl ∷ Context2D → Effect Boolean

getImageSmoothing ∷ ∀ m. MonadCanvasAction m ⇒ m Boolean
getImageSmoothing = withCtx getImageSmoothingImpl

-- | Create a canvas pattern from an image, which can be used as a fill- or
-- | strokeStyle
createPattern
  ∷ ∀ m
  . MonadCanvasAction m
  ⇒ CanvasImageSource
  → PatternRepeat
  → m CanvasPattern
createPattern = withCtx2 C.createPattern

-- | Create a linear gradient from a start point, end point, and a foldable of
-- | color stops.
linearGradient
  ∷ ∀ m color f
  . MonadCanvasAction m
  ⇒ CanvasColor color
  ⇒ Foldable f
  ⇒ LinearGradient
  → f (Tuple Number color)
  → m CanvasGradient
linearGradient grad cols = do
  canvasGradient ← createLinearGradient grad
  for_ cols \(Tuple n col) → addColorStop canvasGradient n col
  pure canvasGradient

-- | Create a radial gradient from a starting circle, ending circle, and a
-- | foldable of color stops.
radialGradient
  ∷ ∀ m color f
  . MonadCanvasAction m
  ⇒ CanvasColor color
  ⇒ Foldable f
  ⇒ RadialGradient
  → f (Tuple Number color)
  → m CanvasGradient
radialGradient grad cols = do
  canvasGradient ← createRadialGradient grad
  for_ cols \(Tuple n col) → addColorStop canvasGradient n col
  pure canvasGradient

-- | Constructs a blank linear `CanvasGradient` that can be modified with
-- | `addColorStop`.
createLinearGradient
  ∷ ∀ m. MonadCanvasAction m ⇒ LinearGradient → m CanvasGradient
createLinearGradient = withCtx1 C.createLinearGradient

-- | Constructs a blank radial `CanvasGradient` that can be modified with
-- | `addColorStop`.
createRadialGradient
  ∷ ∀ m. MonadCanvasAction m ⇒ RadialGradient → m CanvasGradient
createRadialGradient = withCtx1 C.createRadialGradient

-- | Note: Mutates the original `CanvasGradient` and returns `Unit`.
-- | It is recommended to construct gradients with `linearGradient` and
-- | `radialGradient` instead.
addColorStop
  ∷ ∀ m color
  . MonadEffect m
  ⇒ CanvasColor color
  ⇒ CanvasGradient
  → Number
  → color
  → m Unit

addColorStop grad n col = liftEffect $ C.addColorStop grad n (toColorRep col)

-- | Saves the context, see [`save` on MDN](https://developer.mozilla.org/en-US/docs/Web/API/CanvasRenderingContext2D/save)
save ∷ ∀ m. MonadCanvasAction m ⇒ m Unit
save = withCtx C.save

-- | Restores the context, see [`restore` on MDN](https://developer.mozilla.org/en-US/docs/Web/API/CanvasRenderingContext2D/restore)
restore ∷ ∀ m. MonadCanvasAction m ⇒ m Unit
restore = withCtx C.restore

-- | Runs `save`, then the provided action, then `restore`
restoreAfter ∷ ∀ m a. MonadCanvasAction m ⇒ m a → m a
restoreAfter action = save *> action <* restore
