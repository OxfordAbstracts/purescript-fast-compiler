module Graphics.Canvas.Free where

import Prelude

import Color (Color, toHexString)
import Control.Monad.Cont (class MonadTrans, lift)
import Control.Monad.Free (Free, liftF, runFreeM)
import Control.Monad.Reader (ReaderT, ask, runReaderT)
import Control.Monad.Rec.Class (class MonadRec)
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (class MonadEffect, liftEffect)
import Graphics.Canvas (Arc, BezierCurve, CanvasElement, CanvasGradient, CanvasImageSource, CanvasPattern, Composite, Context2D, Dimensions, ImageData, LineCap, LineJoin, LinearGradient, PatternRepeat, QuadraticCurve, RadialGradient, Rectangle, ScaleTransform, TextAlign, TextBaseline, TextMetrics, Transform, TranslateTransform, getContext2D)
import Graphics.Canvas as G
import Graphics.Canvas.Extra (JpegQuality, newOffScreenCanvas)
import Graphics.Canvas.Extra as E
import Unsafe.Coerce (unsafeCoerce)
import Web.DOM.Element (DOMRect)
import Web.DOM.Element as W
import Web.File.Blob (Blob)

type CanvasContext =
  { canvasElement :: CanvasElement
  , context2D :: Context2D
  }

type Coordinate = { x :: Number, y :: Number }

newtype Font = Font String

newtype CanvasT m a = CanvasT (Free (CanvasF m) a) 

instance MonadTrans CanvasT where
  lift = liftC <<< Lift

instance MonadEffect m => MonadEffect (CanvasT m) where
  liftEffect = lift <<< liftEffect

instance MonadAff m => MonadAff (CanvasT m) where
  liftAff = lift <<< liftAff

derive newtype instance MonadRec (CanvasT m)
derive newtype instance Functor (CanvasT m)
derive newtype instance Apply (CanvasT m)
derive newtype instance Applicative (CanvasT m)
derive newtype instance Bind (CanvasT m)
derive newtype instance Monad (CanvasT m)

withOffScreenCanvas :: forall m a. MonadAff m => MonadRec m => Dimensions -> CanvasT m a -> m a
withOffScreenCanvas d f = do
  canvasElement <- liftEffect $ newOffScreenCanvas d
  context2D <- liftEffect $ getContext2D canvasElement
  runReaderT (runCanvasT f) { canvasElement, context2D }

runCanvasT :: forall m a .
              MonadAff m
           => MonadRec m
           => CanvasT m a
           -> ReaderT CanvasContext m a
runCanvasT = runFreeM go <<< (\(CanvasT f) -> f)
  where
    go (Lift f) = lift f
    go (GetWidth a) = do
      { canvasElement } <- ask
      liftEffect $ a <$> G.getCanvasWidth canvasElement
    go (SetWidth w a) = do
      { canvasElement } <- ask
      liftEffect $ G.setCanvasWidth canvasElement w
      pure a
    go (GetHeight a) = do
      { canvasElement } <- ask
      liftEffect $ a <$> G.getCanvasHeight canvasElement
    go (SetHeight h a) = do
      { canvasElement } <- ask
      liftEffect $ G.setCanvasHeight canvasElement h
      pure a
    go (GetDimensions a) = do
      { canvasElement } <- ask
      liftEffect $ a <$> G.getCanvasDimensions canvasElement
    go (SetDimensions d a) = do
      { canvasElement } <- ask
      liftEffect $ G.setCanvasDimensions canvasElement d
      pure a
    go (GetBoundingClientRect a) = do
      { canvasElement } <- ask
      liftEffect $ a <$> W.getBoundingClientRect (unsafeCoerce canvasElement)
    go (ToDataURL a) = do
      { canvasElement } <- ask
      liftEffect $ a <$> G.canvasToDataURL canvasElement
    go (SetLineWidth w a) = do
      { context2D } <- ask
      liftEffect $ G.setLineWidth context2D w
      pure a
    go (SetLineDash d a) = do
      { context2D } <- ask
      liftEffect $ G.setLineDash context2D d
      pure a
    go (SetFillColor c a) = do
      { context2D } <- ask
      liftEffect $ G.setFillStyle context2D (toHexString c)
      pure a
    go (SetStrokeColor c a) = do
      { context2D } <- ask
      liftEffect $ G.setStrokeStyle context2D (toHexString c)
      pure a
    go (SetShadowBlurRadius r a) = do
      { context2D } <- ask
      liftEffect $ G.setShadowBlur context2D r 
      pure a
    go (SetShadowOffsetX x a) = do
      { context2D } <- ask
      liftEffect $ G.setShadowOffsetX context2D x 
      pure a
    go (SetShadowOffsetY y a) = do
      { context2D } <- ask
      liftEffect $ G.setShadowOffsetY context2D y 
      pure a
    go (SetShadowColor c a) = do
      { context2D } <- ask
      liftEffect $ G.setShadowColor context2D (toHexString c)
      pure a
    go (SetMiterLimit l a) = do
      { context2D } <- ask
      liftEffect $ G.setMiterLimit context2D l 
      pure a
    go (SetLineCap l a) = do
      { context2D } <- ask
      liftEffect $ G.setLineCap context2D l 
      pure a
    go (SetLineJoin l a) = do
      { context2D } <- ask
      liftEffect $ G.setLineJoin context2D l 
      pure a
    go (SetCompositeOperation o a) = do
      { context2D } <- ask
      liftEffect $ G.setGlobalCompositeOperation context2D o 
      pure a
    go (SetAlpha n a) = do
      { context2D } <- ask
      liftEffect $ G.setGlobalAlpha context2D n 
      pure a
    go (BeginPath a) = do
      { context2D } <- ask
      liftEffect $ G.beginPath context2D 
      pure a
    go (Stroke a) = do
      { context2D } <- ask
      liftEffect $ G.stroke context2D 
      pure a
    go (Fill a) = do
      { context2D } <- ask
      liftEffect $ G.fill context2D 
      pure a
    go (Clip a) = do
      { context2D } <- ask
      liftEffect $ G.clip context2D 
      pure a
    go (LineTo xy a) = do
      { context2D } <- ask
      liftEffect $ G.lineTo context2D xy.x xy.y
      pure a
    go (MoveTo xy a) = do
      { context2D } <- ask
      liftEffect $ G.moveTo context2D xy.x xy.y
      pure a
    go (ClosePath a) = do
      { context2D } <- ask
      liftEffect $ G.closePath context2D 
      pure a
    go (DrawArc r a) = do
      { context2D } <- ask
      liftEffect $ G.arc context2D r 
      pure a
    go (Rect r a) = do
      { context2D } <- ask
      liftEffect $ G.rect context2D r 
      pure a
    go (FillRect r a) = do
      { context2D } <- ask
      liftEffect $ G.fillRect context2D r 
      pure a
    go (StrokeRect r a) = do
      { context2D } <- ask
      liftEffect $ G.strokeRect context2D r 
      pure a
    go (ClearRect r a) = do
      { context2D } <- ask
      liftEffect $ G.clearRect context2D r 
      pure a
    go (Scale s a) = do
      { context2D } <- ask
      liftEffect $ G.scale context2D s 
      pure a
    go (Rotate r a) = do
      { context2D } <- ask
      liftEffect $ G.rotate context2D r 
      pure a
    go (Translate t a) = do
      { context2D } <- ask
      liftEffect $ G.translate context2D t 
      pure a
    go (ApplyTransform t a) = do
      { context2D } <- ask
      liftEffect $ G.transform context2D t 
      pure a
    go (SetTransform t a) = do
      { context2D } <- ask
      liftEffect $ G.setTransform context2D t 
      pure a
    go (GetTextAlign a) = do
      { context2D } <- ask
      liftEffect $ a <$> G.textAlign context2D 
    go (SetTextAlign d a) = do
      { context2D } <- ask
      liftEffect $ G.setTextAlign context2D d
      pure a
    go (GetTextBaseline a) = do
      { context2D } <- ask
      liftEffect $ a <$> G.textBaseline context2D 
    go (SetTextBaseline d a) = do
      { context2D } <- ask
      liftEffect $ G.setTextBaseline context2D d
      pure a
    go (GetFont a) = do
      { context2D } <- ask
      liftEffect $ a <<< Font <$> G.font context2D 
    go (SetFont (Font d) a) = do
      { context2D } <- ask
      liftEffect $ G.setFont context2D d
      pure a
    go (FillText txt xy a) = do
      { context2D } <- ask
      liftEffect $ G.fillText context2D txt xy.x xy.y
      pure a
    go (StrokeText txt xy a) = do
      { context2D } <- ask
      liftEffect $ G.strokeText context2D txt xy.x xy.y
      pure a
    go (MeasureText txt a) = do
      { context2D } <- ask
      liftEffect $ a <$> G.measureText context2D txt
    go (Save a) = do
      { context2D } <- ask
      liftEffect $ G.save context2D
      pure a
    go (Restore a) = do
      { context2D } <- ask
      liftEffect $ G.restore context2D
      pure a
    go (GetImageData r a) = do
      { context2D } <- ask
      liftEffect $ a <$> G.getImageData context2D r.x r.y r.width r.height
    go (PutImageData i xy a) = do
      { context2D } <- ask
      liftEffect $ G.putImageData context2D i xy.x xy.y
      pure a
    go (PutImageDataRect i xy c a) = do
      { context2D } <- ask
      liftEffect $ G.putImageDataFull context2D i xy.x xy.y c.x c.y c.width c.height
      pure a
    go (BlankImageData d a) = do
      { context2D } <- ask 
      liftEffect $ a <$> G.createImageData context2D d.width d.height
    go (ToImageSource a) = do
      { canvasElement } <- ask
      pure $ a $ G.canvasElementToImageSource canvasElement
    go (DrawImage s c a) = do
      { context2D } <- ask
      liftEffect $ G.drawImage context2D s c.x c.y
      pure a
    go (DrawImageScale s d a) = do
      { context2D } <- ask
      liftEffect $ G.drawImageScale context2D s d.x d.y d.width d.height
      pure a
    go (DrawImageRectScale s st a) = do
      { context2D } <- ask
      let r = st.source
          c = st.target
      liftEffect $ G.drawImageFull context2D s r.x r.y r.width r.height c.x c.y c.width c.height
      pure a
    go (CreatePattern i p a) = do
      { context2D } <- ask
      liftEffect $ a <$> G.createPattern context2D i p
    go (SetPatternFillStyle p a) = do
      { context2D } <- ask
      liftEffect $ G.setPatternFillStyle context2D p
      pure a
    go (CreateLinearGradient g a) = do
      { context2D } <- ask
      liftEffect $ a <$> G.createLinearGradient context2D g
    go (CreateRadialGradient g a) = do
      { context2D } <- ask
      liftEffect $ a <$> G.createRadialGradient context2D g
    go (SetGradientFillStyle g a) = do
      { context2D } <- ask
      liftEffect $ G.setGradientFillStyle context2D g
      pure a
    go (QuadraticCurveTo c a) = do
      { context2D } <- ask
      liftEffect $ G.quadraticCurveTo context2D c
      pure a
    go (BezierCurveTo c a) = do
      { context2D } <- ask
      liftEffect $ G.bezierCurveTo context2D c
      pure a
    go (ConvertToJpegBlob q a) = do
      { canvasElement } <- ask
      liftAff $ a <$> E.convertToJpegBlob canvasElement q

getWidth :: forall m. CanvasT m Number
getWidth = liftC $ GetWidth identity

setWidth :: forall m. Number -> CanvasT m Unit
setWidth w = liftC $ SetWidth w unit

getHeight :: forall m. CanvasT m Number
getHeight = liftC $ GetHeight identity

setHeight :: forall m. Number -> CanvasT m Unit
setHeight h = liftC $ SetHeight h unit

getDimensions :: forall m. CanvasT m Dimensions 
getDimensions = liftC $ GetDimensions identity

setDimensions :: forall m. Dimensions -> CanvasT m Unit
setDimensions d = liftC $ SetDimensions d unit

getBoundingClientRect :: forall m. CanvasT m DOMRect
getBoundingClientRect = liftC $ GetBoundingClientRect identity

toDataURL :: forall m. CanvasT m String
toDataURL = liftC $ ToDataURL identity

setLineWidth :: forall m. Number -> CanvasT m Unit
setLineWidth w = liftC $ SetLineWidth w unit

setLineDash :: forall m. Array Number -> CanvasT m Unit
setLineDash d = liftC $ SetLineDash d unit

setFillColor :: forall m. Color -> CanvasT m Unit
setFillColor c = liftC $ SetFillColor c unit

setStrokeColor :: forall m. Color -> CanvasT m Unit
setStrokeColor c = liftC $ SetStrokeColor c unit

setShadowBlurRadius :: forall m. Number -> CanvasT m Unit
setShadowBlurRadius r = liftC $ SetShadowBlurRadius r unit

setShadowOffsetX :: forall m. Number -> CanvasT m Unit
setShadowOffsetX x = liftC $ SetShadowOffsetX x unit

setShadowOffsetY :: forall m. Number -> CanvasT m Unit
setShadowOffsetY y = liftC $ SetShadowOffsetY y unit

setShadowColor :: forall m. Color -> CanvasT m Unit
setShadowColor c = liftC $ SetShadowColor c unit

setMiterLimit :: forall m. Number -> CanvasT m Unit
setMiterLimit l = liftC $ SetMiterLimit l unit

setLineCap :: forall m. LineCap -> CanvasT m Unit
setLineCap l = liftC $ SetLineCap l unit

setLineJoin :: forall m. LineJoin -> CanvasT m Unit
setLineJoin l = liftC $ SetLineJoin l unit

setCompositeOperation :: forall m. Composite -> CanvasT m Unit
setCompositeOperation o = liftC $ SetCompositeOperation o unit

setAlpha :: forall m. Number -> CanvasT m Unit
setAlpha n = liftC $ SetAlpha n unit

beginPath :: forall m. CanvasT m Unit
beginPath = liftC $ BeginPath unit

stroke :: forall m. CanvasT m Unit
stroke = liftC $ Stroke unit

fill :: forall m. CanvasT m Unit
fill = liftC $ Fill unit

clip :: forall m. CanvasT m Unit
clip = liftC $ Clip unit

lineTo :: forall m. Coordinate -> CanvasT m Unit
lineTo xy = liftC $ LineTo xy unit

moveTo :: forall m. Coordinate -> CanvasT m Unit
moveTo xy = liftC $ MoveTo xy unit

closePath :: forall m. CanvasT m Unit
closePath = liftC $ ClosePath unit

arc :: forall m. Arc -> CanvasT m Unit
arc a = liftC $ DrawArc a unit

rect :: forall m. Rectangle -> CanvasT m Unit
rect r = liftC $ Rect r unit

fillRect :: forall m. Rectangle -> CanvasT m Unit
fillRect r = liftC $ FillRect r unit

strokeRect :: forall m. Rectangle -> CanvasT m Unit
strokeRect r = liftC $ StrokeRect r unit

clearRect :: forall m. Rectangle -> CanvasT m Unit
clearRect r = liftC $ ClearRect r unit

scale :: forall m. ScaleTransform -> CanvasT m Unit
scale s = liftC $ Scale s unit

rotate :: forall m. Number -> CanvasT m Unit
rotate r = liftC $ Rotate r unit

translate :: forall m. TranslateTransform -> CanvasT m Unit
translate t = liftC $ Translate t unit

transform :: forall m. Transform -> CanvasT m Unit
transform t = liftC $ ApplyTransform t unit

setTransform :: forall m. Transform -> CanvasT m Unit
setTransform t = liftC $ SetTransform t unit

getTextAlign :: forall m. CanvasT m TextAlign
getTextAlign = liftC $ GetTextAlign identity

setTextAlign :: forall m. TextAlign -> CanvasT m Unit
setTextAlign t = liftC $ SetTextAlign t unit

getTextBaseline :: forall m. CanvasT m TextBaseline
getTextBaseline = liftC $ GetTextBaseline identity

setTextBaseline :: forall m. TextBaseline -> CanvasT m Unit
setTextBaseline t = liftC $ SetTextBaseline t unit

getFont :: forall m. CanvasT m Font 
getFont = liftC $ GetFont identity

setFont :: forall m. Font -> CanvasT m Unit
setFont t = liftC $ SetFont t unit

fillText :: forall m. String -> Coordinate -> CanvasT m Unit 
fillText txt xy = liftC $ FillText txt xy unit

strokeText :: forall m. String -> Coordinate -> CanvasT m Unit 
strokeText txt xy = liftC $ StrokeText txt xy unit

measureText :: forall m. String -> CanvasT m TextMetrics
measureText txt = liftC $ MeasureText txt identity

save :: forall m. CanvasT m Unit
save = liftC $ Save unit

restore :: forall m. CanvasT m Unit
restore = liftC $ Restore unit

withContext :: forall m a. CanvasT m a -> CanvasT m a
withContext f = do
  save
  a <- f
  restore
  pure a

getImageData :: forall m. Rectangle -> CanvasT m ImageData
getImageData r = liftC $ GetImageData r identity

putImageData :: forall m. ImageData -> Coordinate -> CanvasT m Unit
putImageData i c = liftC $ PutImageData i c unit

putImageDataRect :: forall m. ImageData -> Coordinate -> Rectangle -> CanvasT m Unit
putImageDataRect i c r = liftC $ PutImageDataRect i c r unit

blankImageData :: forall m. Dimensions -> CanvasT m ImageData
blankImageData d = liftC $ BlankImageData d identity

canvasImageSource :: forall m. CanvasT m CanvasImageSource
canvasImageSource = liftC $ ToImageSource identity

drawImage :: forall m. CanvasImageSource -> Coordinate -> CanvasT m Unit
drawImage i c = liftC $ DrawImage i c unit

drawImageScale :: forall m. CanvasImageSource -> Rectangle -> CanvasT m Unit
drawImageScale i d = liftC $ DrawImageScale i d unit

drawImageRectScale :: forall m. CanvasImageSource -> { source :: Rectangle, target :: Rectangle } -> CanvasT m Unit
drawImageRectScale i r = liftC $ DrawImageRectScale i r unit

createPattern :: forall m. CanvasImageSource -> PatternRepeat -> CanvasT m CanvasPattern
createPattern i p = liftC $ CreatePattern i p identity

setPatternFillStyle :: forall m. CanvasPattern -> CanvasT m Unit
setPatternFillStyle p = liftC $ SetPatternFillStyle p unit 

createLinearGradient :: forall m. LinearGradient -> CanvasT m CanvasGradient
createLinearGradient g = liftC $ CreateLinearGradient g identity

createRadialGradient :: forall m. RadialGradient -> CanvasT m CanvasGradient
createRadialGradient g = liftC $ CreateRadialGradient g identity

setGradientFillStyle :: forall m. CanvasGradient -> CanvasT m Unit
setGradientFillStyle g = liftC $ SetGradientFillStyle g unit

quadraticCurveTo :: forall m. QuadraticCurve -> CanvasT m Unit
quadraticCurveTo c = liftC $ QuadraticCurveTo c unit

bezierCurveTo :: forall m. BezierCurve -> CanvasT m Unit
bezierCurveTo c = liftC $ BezierCurveTo c unit

convertToJpegBlob :: forall m. JpegQuality -> CanvasT m Blob
convertToJpegBlob q = liftC $ ConvertToJpegBlob q identity



data CanvasF m a =
    Lift (m a)
  | GetWidth (Number -> a)
  | SetWidth Number a
  | GetHeight (Number -> a)
  | SetHeight Number a
  | GetDimensions (Dimensions -> a)
  | SetDimensions Dimensions a
  | GetBoundingClientRect (DOMRect -> a)
  | ToDataURL (String -> a)
  | SetLineWidth Number a
  | SetLineDash (Array Number) a
  | SetFillColor Color a
  | SetStrokeColor Color a
  | SetShadowBlurRadius Number a
  | SetShadowOffsetX Number a
  | SetShadowOffsetY Number a
  | SetShadowColor Color a
  | SetMiterLimit Number a
  | SetLineCap LineCap a
  | SetLineJoin LineJoin a
  | SetCompositeOperation Composite a
  | SetAlpha Number a
  | BeginPath a
  | Stroke a
  | Fill a
  | Clip a
  | LineTo Coordinate a
  | MoveTo Coordinate a
  | ClosePath a
  | DrawArc Arc a
  | Rect Rectangle a
  | FillRect Rectangle a
  | StrokeRect Rectangle a
  | ClearRect Rectangle a
  | Scale ScaleTransform a
  | Rotate Number a
  | Translate TranslateTransform a
  | ApplyTransform Transform a
  | SetTransform Transform a
  | GetTextAlign (TextAlign -> a)
  | SetTextAlign TextAlign a
  | GetTextBaseline (TextBaseline -> a)
  | SetTextBaseline TextBaseline a
  | GetFont (Font -> a)
  | SetFont Font a
  | FillText String Coordinate a
  | StrokeText String Coordinate a
  | MeasureText String (TextMetrics -> a)
  | Save a
  | Restore a
  | GetImageData Rectangle (ImageData -> a)
  | PutImageData ImageData Coordinate a
  | PutImageDataRect ImageData Coordinate Rectangle a
  | BlankImageData Dimensions (ImageData -> a)
  | ToImageSource (CanvasImageSource -> a)
  | DrawImage CanvasImageSource Coordinate a
  | DrawImageScale CanvasImageSource Rectangle a
  | DrawImageRectScale CanvasImageSource { source :: Rectangle, target :: Rectangle } a
  | CreatePattern CanvasImageSource PatternRepeat (CanvasPattern -> a)
  | SetPatternFillStyle CanvasPattern a 
  | CreateLinearGradient LinearGradient (CanvasGradient -> a)
  | CreateRadialGradient RadialGradient (CanvasGradient -> a)
  | SetGradientFillStyle CanvasGradient a
  | QuadraticCurveTo QuadraticCurve a
  | BezierCurveTo BezierCurve a
  | ConvertToJpegBlob JpegQuality (Blob -> a)


instance Functor m => Functor (CanvasF m) where
  map f (Lift q) = Lift (f <$> q)
  map f (GetWidth e) = GetWidth (f <<< e)
  map f (SetWidth w e) = SetWidth w (f e)
  map f (GetHeight e) = GetHeight (f <<< e)
  map f (SetHeight h e) = SetHeight h (f e)
  map f (GetDimensions e) = GetDimensions (f <<< e)
  map f (SetDimensions d e) = SetDimensions d (f e)
  map f (GetBoundingClientRect e) = GetBoundingClientRect (f <<< e)
  map f (ToDataURL e) = ToDataURL (f <<< e)
  map f (SetLineWidth w e) = SetLineWidth w (f e)
  map f (SetLineDash d e) = SetLineDash d (f e)
  map f (SetFillColor c e) = SetFillColor c (f e)
  map f (SetStrokeColor c e) = SetStrokeColor c (f e)
  map f (SetShadowBlurRadius r e) = SetShadowBlurRadius r (f e)
  map f (SetShadowOffsetX x e) = SetShadowOffsetX x (f e)
  map f (SetShadowOffsetY y e) = SetShadowOffsetY y (f e)
  map f (SetShadowColor c e) = SetShadowColor c (f e)
  map f (SetMiterLimit l e) = SetMiterLimit l (f e)
  map f (SetLineCap l e) = SetLineCap l (f e)
  map f (SetLineJoin l e) = SetLineJoin l (f e)
  map f (SetCompositeOperation o e) = SetCompositeOperation o (f e)
  map f (SetAlpha a e) = SetAlpha a (f e)
  map f (BeginPath e) = BeginPath (f e)
  map f (Stroke e) = Stroke (f e)
  map f (Fill e) = Fill (f e)
  map f (Clip e) = Clip (f e)
  map f (LineTo xy e) = LineTo xy (f e)
  map f (MoveTo xy e) = MoveTo xy (f e)
  map f (ClosePath e) = ClosePath (f e)
  map f (DrawArc a e) = DrawArc a (f e)
  map f (Rect r e) = Rect r (f e)
  map f (FillRect r e) = FillRect r (f e)
  map f (StrokeRect r e) = StrokeRect r (f e)
  map f (ClearRect r e) = ClearRect r (f e)
  map f (Scale s e) = Scale s (f e)
  map f (Rotate r e) = Rotate r (f e)
  map f (Translate t e) = Translate t (f e)
  map f (ApplyTransform t e) = ApplyTransform t (f e)
  map f (SetTransform t e) = SetTransform t (f e)
  map f (GetTextAlign e) = GetTextAlign (f <<< e)
  map f (SetTextAlign t e) = SetTextAlign t (f e)
  map f (GetTextBaseline e) = GetTextBaseline (f <<< e)
  map f (SetTextBaseline t e) = SetTextBaseline t (f e)
  map f (GetFont e) = GetFont (f <<< e)
  map f (SetFont t e) = SetFont t (f e)
  map f (FillText txt xy e) = FillText txt xy (f e)
  map f (StrokeText txt xy e) = StrokeText txt xy (f e)
  map f (MeasureText txt e) = MeasureText txt (f <<< e)
  map f (Save e) = Save (f e)
  map f (Restore e) = Restore (f e)
  map f (GetImageData r e) = GetImageData r (f <<< e)
  map f (PutImageData i c e) = PutImageData i c (f e)
  map f (PutImageDataRect i c r e) = PutImageDataRect i c r (f e)
  map f (BlankImageData d e) = BlankImageData d (f <<< e)
  map f (ToImageSource e) = ToImageSource (f <<< e)
  map f (DrawImage i c e) = DrawImage i c (f e)
  map f (DrawImageScale i d e) = DrawImageScale i d (f e)
  map f (DrawImageRectScale i st e) = DrawImageRectScale i st (f e)
  map f (CreatePattern i p e) = CreatePattern i p (f <<< e)
  map f (SetPatternFillStyle p e) = SetPatternFillStyle p (f e)
  map f (CreateLinearGradient g e) = CreateLinearGradient g (f <<< e)
  map f (CreateRadialGradient g e) = CreateRadialGradient g (f <<< e)
  map f (SetGradientFillStyle g e) = SetGradientFillStyle g (f e)
  map f (QuadraticCurveTo c e) = QuadraticCurveTo c (f e)
  map f (BezierCurveTo c e) = BezierCurveTo c (f e)
  map f (ConvertToJpegBlob q e) = ConvertToJpegBlob q (f <<< e)



liftC :: forall m a. CanvasF m a -> CanvasT m a
liftC = CanvasT <<< liftF


