module XTerm.Buffer.Line
  ( BufferLine
  , isWrapped
  , length
  , getCell
  , translateToString
  ) where
import Control.Alt ((<$>))
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Foreign (Foreign)
import XTerm.Buffer.Cell (BufferCell)
import XTerm.Utils (maybeUndefined)

data BufferLine

foreign import isWrapped :: BufferLine -> Effect Boolean
foreign import length :: BufferLine -> Effect Int

foreign import _getCell :: BufferLine -> Int -> Effect Foreign
foreign import _getCellOpt :: BufferLine -> Int -> BufferCell -> Effect Foreign

getCell :: BufferLine -> Int -> Maybe BufferCell -> Effect (Maybe BufferCell)
getCell b i Nothing = maybeUndefined <$> _getCell b i
getCell b i (Just c) = maybeUndefined <$> _getCellOpt b i c

foreign import translateToString :: BufferLine -> Boolean -> Int -> Int -> Effect String

