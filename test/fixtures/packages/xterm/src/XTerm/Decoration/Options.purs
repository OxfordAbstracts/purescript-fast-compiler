module XTerm.Decoration.Options where

import Color (Color, toHexString)
import Data.Maybe (Maybe(..))
import Data.Op (Op(..))
import Data.Options (Option, Options(..), opt)
import Data.Tuple (Tuple(..))
import Foreign (unsafeToForeign)
import XTerm.Marker (Marker)
import XTerm.Options.Theme (copt)

type DecorationOptions =
  { marker :: Marker
  , decorationOptions :: Options OptionalDecoration
  }

data IDecorationOptions
foreign import makeDecorationOptions :: DecorationOptions -> IDecorationOptions

type DecorationOption = Option OptionalDecoration

data OptionalDecoration

data Anchor = AnchorLeft | AnchorRight

anchorString :: Anchor -> String
anchorString AnchorLeft = "left"
anchorString _ = "right"

anchor :: DecorationOption Anchor
anchor = Op (\v -> Options [ Tuple "anchor" (unsafeToForeign (anchorString v)) ]) 

xOffset :: DecorationOption Number
xOffset = opt "x"

width :: DecorationOption Int
width = opt "width"

height :: DecorationOption Int
height = opt "height"

backgroundColor :: DecorationOption Color
backgroundColor = copt "backgroundColor"

foregroundColor :: DecorationOption Color
foregroundColor = copt "foregroundColor"

data Layer = Bottom | Top

layerString :: Layer -> String
layerString Bottom = "bottom"
layerString _ = "top"

layer :: DecorationOption Layer
layer = Op (\v -> Options [ Tuple "layer" (unsafeToForeign (layerString v)) ]) 

data Position = PositionLeft | PositionCenter | PositionRight | PositionFull 

positionString :: Position -> String
positionString PositionLeft = "left"
positionString PositionCenter = "center"
positionString PositionRight = "right"
positionString PositionFull = "full"

type OverviewRulerOptions =
  { color :: Color
  , position :: Maybe Position
  }

overviewRulerOptions :: DecorationOption OverviewRulerOptions
overviewRulerOptions = Op (\v -> Options [ Tuple "overviewRulerOptions" (toForeign v) ])
  where
    toForeign { color, position } =
      case position of
        Nothing -> unsafeToForeign { color: toHexString color }
        Just p -> unsafeToForeign { color: toHexString color, position: positionString p }


