module XTerm.Buffer
  ( Buffer
  , CellPosition(..)
  , BufferRange(..)
  , BufferType(..)
  , bufferType
  , cursorY
  , cursorX
  , viewportY
  , baseY
  , length
  , getLine
  , getNullCell
  ) where
import Prelude
import Data.Maybe (Maybe)
import Effect (Effect)
import Foreign (Foreign)
import XTerm.Buffer.Cell (BufferCell)
import XTerm.Buffer.Line (BufferLine)
import XTerm.Utils (maybeUndefined)

type CellPosition =
  { x :: Int
  , y :: Int
  }

type BufferRange =
  { start :: CellPosition
  , end :: CellPosition
  }

data Buffer

data BufferType = Normal | Alternate

foreign import _bufferType :: Buffer -> Effect String

bufferType :: Buffer -> Effect BufferType
bufferType b = do
  e <- _bufferType b
  case e of
    "normal" -> pure Normal
    _ -> pure Alternate

foreign import cursorY :: Buffer -> Effect Int
foreign import cursorX :: Buffer -> Effect Int
foreign import viewportY :: Buffer -> Effect Int
foreign import baseY :: Buffer -> Effect Int
foreign import length :: Buffer -> Effect Int
foreign import _getLine :: Buffer -> Int -> Effect Foreign

getLine :: Buffer -> Int -> Effect (Maybe BufferLine)
getLine buffer i = maybeUndefined <$> _getLine buffer i

foreign import getNullCell :: Buffer -> Effect BufferCell

