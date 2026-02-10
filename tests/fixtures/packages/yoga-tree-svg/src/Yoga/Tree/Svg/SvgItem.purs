module Yoga.Tree.Svg.SvgItem where

import Data.Maybe (Maybe)

import Yoga.JSON (class WriteForeign, class ReadForeign)
import Yoga.Tree.Extended.Path (Path)

class (WriteForeign a, ReadForeign a) <= IsTreeItem a where
  default :: a
  _export :: a -> String
  _import :: String -> Maybe a


class (IsTreeItem a) <= IsSvgTreeItem a where
  foldLabel :: a -> String
  pinnedLine :: Path -> a -> String