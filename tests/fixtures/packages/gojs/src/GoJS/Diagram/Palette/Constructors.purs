module GoJS.Diagram.Palette.Constructors where

import Effect (Effect)
import GoJS.Diagram.Types (Palette_)
import GoJS.Unsafe.Constructor (constructor1)

newPalette :: String -> Effect Palette_
newPalette = constructor1 "Palette"
