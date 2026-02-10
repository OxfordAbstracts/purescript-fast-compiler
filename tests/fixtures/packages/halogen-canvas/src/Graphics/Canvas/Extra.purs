module Graphics.Canvas.Extra
  ( newOffScreenCanvas
  , JpegQuality(..)
  , convertToJpegBlob
  , canvasImageSourceWidth
  , canvasImageSourceHeight
  ) where

import Prelude

import Control.Promise (Promise, toAffE)
import Effect (Effect)
import Effect.Aff (Aff)
import Graphics.Canvas (CanvasElement, CanvasImageSource, Dimensions)
import Web.File.Blob (Blob)

foreign import _newOffScreenCanvas :: Number -> Number -> Effect CanvasElement

newOffScreenCanvas :: Dimensions -> Effect CanvasElement
newOffScreenCanvas d = _newOffScreenCanvas d.width d.height

foreign import _convertToJpegBlob :: CanvasElement -> Number -> Effect (Promise Blob) 

newtype JpegQuality = JpegQuality Number

convertToJpegBlob :: CanvasElement -> JpegQuality -> Aff Blob
convertToJpegBlob c (JpegQuality q) = toAffE $ _convertToJpegBlob c q

foreign import canvasImageSourceWidth :: CanvasImageSource -> Number
foreign import canvasImageSourceHeight :: CanvasImageSource -> Number

