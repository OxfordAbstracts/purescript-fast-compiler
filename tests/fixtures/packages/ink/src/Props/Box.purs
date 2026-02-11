module Props.Box where

import Data.Maybe (Maybe(..))
import Internal.ForeignUtils (PossiblyUndefined)
import React.Basic (JSX)

type BoxPropRows :: forall k. (Type -> k) -> Row k
type BoxPropRows f =
  ( padding :: f Number
  , flexDirection :: f String
  , marginTop :: f Int
  , marginBottom :: f Int
  , backgroundColor :: f String
  , width :: f String
  , justifyContent :: f String
  , height :: f String
  )

type BoxPropRecord f = Record (BoxPropRows f)

mapBoxProps :: forall f g. (forall a. f a -> g a) -> BoxPropRecord f -> BoxPropRecord g
mapBoxProps f props =
  props
    { padding = f props.padding
    , flexDirection = f props.flexDirection
    , marginTop = f props.marginTop
    , marginBottom = f props.marginBottom
    , backgroundColor = f props.backgroundColor
    , width = f props.width
    , justifyContent = f props.justifyContent
    , height = f props.height
    }

type BoxPropsComplete = Record (children :: Array JSX | BoxPropRows PossiblyUndefined)

defaultBoxProps :: BoxPropRecord Maybe
defaultBoxProps =
  { padding: Just 0.0
  , flexDirection: Just "row"
  , marginTop: Just 0
  , marginBottom: Just 0
  , backgroundColor: Nothing
  , width: Nothing
  , justifyContent: Nothing
  , height: Nothing
  }
