module XTerm.Buffer.Cell where

import Effect (Effect)

data BufferCell

foreign import getWidth :: BufferCell -> Effect Int
foreign import getChars :: BufferCell -> Effect String
foreign import getCode :: BufferCell -> Effect Int
foreign import getFgColorMode :: BufferCell -> Effect Int
foreign import getBgColorMode :: BufferCell -> Effect Int
foreign import getFgColor :: BufferCell -> Effect Int
foreign import getBgColor :: BufferCell -> Effect Int
foreign import isBold :: BufferCell -> Effect Int
foreign import isItalic :: BufferCell -> Effect Int
foreign import isDim :: BufferCell -> Effect Int
foreign import isUnderline :: BufferCell -> Effect Int
foreign import isBlink :: BufferCell -> Effect Int
foreign import isInverse :: BufferCell -> Effect Int
foreign import isInvisible :: BufferCell -> Effect Int
foreign import isStrikethrough :: BufferCell -> Effect Int
foreign import isOverline :: BufferCell -> Effect Int
foreign import isFgRGB :: BufferCell -> Effect Boolean
foreign import isBgRGB :: BufferCell -> Effect Boolean
foreign import isFgPalette :: BufferCell -> Effect Boolean
foreign import isBgPalette :: BufferCell -> Effect Boolean
foreign import isFgDefault :: BufferCell -> Effect Boolean
foreign import isBgDefault :: BufferCell -> Effect Boolean
foreign import isAttributeDefault :: BufferCell -> Effect Boolean

