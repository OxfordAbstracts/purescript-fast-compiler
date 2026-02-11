module Props.Text where

import Data.Maybe (Maybe(..))
import Internal.ForeignUtils (PossiblyUndefined)
import React.Basic (JSX)

type TextPropRows :: forall k. (Type -> k) -> Row k
type TextPropRows f =
  ( color :: f String
  , backgroundColor :: f String
  , dimColor :: f Boolean
  , bold :: f Boolean
  , italic :: f Boolean
  , underline :: f Boolean
  , strikethrough :: f Boolean
  , inverse :: f Boolean
  , wrap :: f Boolean
  )

type TextPropRecord f = Record (TextPropRows f)

mapTextProps
  :: forall f g. (forall a. f a -> g a) -> TextPropRecord f -> TextPropRecord g
mapTextProps f props =
  props
    { color = f props.color
    , backgroundColor = f props.backgroundColor
    , dimColor = f props.dimColor
    , bold = f props.bold
    , italic = f props.italic
    , underline = f props.underline
    , strikethrough = f props.strikethrough
    , inverse = f props.inverse
    , wrap = f props.wrap
    }

type TextPropsComplete = Record (children :: Array JSX | TextPropRows PossiblyUndefined)

defaultTextProps :: TextPropRecord Maybe
defaultTextProps =
  { color: Nothing
  , backgroundColor: Nothing
  , dimColor: Nothing
  , bold: Nothing
  , italic: Nothing
  , underline: Nothing
  , strikethrough: Nothing
  , inverse: Nothing
  , wrap: Nothing
  }
