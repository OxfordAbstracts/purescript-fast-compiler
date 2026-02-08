module XTerm.Options.Theme where

import Color

import Control.Category ((<<<))
import Data.Op (Op(..))
import Data.Options (Option, Options(..), opt)
import Data.Tuple (Tuple(..))
import Foreign (unsafeToForeign)

data Theme

type ColorOption = Option Theme Color

copt :: forall opt . String -> Op (Options opt) Color
copt = Op <<< colorOpt
  where
    colorOpt k v = Options [ Tuple k (unsafeToForeign (toHexString v)) ]

foreground :: ColorOption
foreground = copt "foreground"

background :: ColorOption
background = copt "background"

cursor :: ColorOption
cursor = copt "cursor"

cursorAccent :: ColorOption
cursorAccent = copt "cursorAccent"

selectionBackground :: ColorOption
selectionBackground = copt "selectionBackground"

selectionForeground :: ColorOption
selectionForeground = copt "selectionForeground"

selectionInactiveBackground :: ColorOption
selectionInactiveBackground = copt "selectionInactiveBackground"

black :: ColorOption
black = copt "black"

red :: ColorOption
red = copt "red"

green :: ColorOption
green = copt "green"

yellow :: ColorOption
yellow = copt "yellow"

blue :: ColorOption
blue = copt "blue"

magenta :: ColorOption
magenta = copt "magenta"

cyan :: ColorOption
cyan = copt "cyan"

white :: ColorOption
white = copt "white"

brightBlack :: ColorOption
brightBlack = copt "brightBlack"

brightRed :: ColorOption
brightRed = copt "brightRed"

brightGreen :: ColorOption
brightGreen = copt "brightGreen"

brightYellow :: ColorOption
brightYellow = copt "brightYellow"

brightBlue :: ColorOption
brightBlue = copt "brightBlue"

brightMagenta :: ColorOption
brightMagenta = copt "brightMagenta"

brightCyan :: ColorOption
brightCyan = copt "brightCyan"

brightWhite :: ColorOption
brightWhite = copt "brightWhite"

extendedAnsi :: Option Theme (Array String)
extendedAnsi = opt "extendedAnsi"

