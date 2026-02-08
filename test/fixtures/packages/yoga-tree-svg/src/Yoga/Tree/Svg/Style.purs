module Yoga.Tree.Svg.Style where

import Prelude

import Halogen.Svg.Attributes (Color(..), printColor) as HSA


data Theme
    = Dark
    | Light


type C = Theme -> HSA.Color


background :: C
background Light = HSA.RGB 255 255 240
background Dark = HSA.RGB 16 15 15

background2 :: C
background2 Light = HSA.RGB 242 240 229
background2 Dark = HSA.RGB 28 27 26

ui :: C
ui Light =  HSA.RGB 230 228 217
ui Dark =  HSA.RGB 40 39 38

ui2 :: C
ui2 Light = HSA.RGB 218 216 206
ui2 Dark = HSA.RGB 52 51 49

ui3 :: C
ui3 Light = HSA.RGB 206 205 195
ui3 Dark = HSA.RGB 64 62 60

tx3 :: C
tx3 Light = HSA.RGB 183 181 172
tx3 Dark = HSA.RGB 87 86 83

tx2 :: C
tx2 Light = HSA.RGB 111 110 105
tx2 Dark = HSA.RGB 135 133 128

tx :: C
tx Light = HSA.RGB 16 15 15
tx Dark = HSA.RGB 206 205 195

reA :: C
reA Light = HSA.RGB 209 77 65
reA Dark = HSA.RGB 175 48 41

reB :: C
reB Light = HSA.RGB 175 48 41
reB Dark = HSA.RGB 209 77 65

orA :: C
orA Light = HSA.RGB 218 112 44
orA Dark = HSA.RGB 188 82 21

orB :: C
orB Light = HSA.RGB 188 82 21
orB Dark = HSA.RGB 218 112 44

yeA :: C
yeA Light = HSA.RGB 208 162 21
yeA Dark = HSA.RGB 173 131 1

yeB :: C
yeB Light = HSA.RGB 173 131 1
yeB Dark = HSA.RGB 208 162 21

grA :: C
grA Light = HSA.RGB 135 154 57
grA Dark = HSA.RGB 102 128 11

grB :: C
grB Light = HSA.RGB 102 128 11
grB Dark = HSA.RGB 135 154 57

cyA :: C
cyA Light = HSA.RGB 58 169 159
cyA Dark = HSA.RGB 36 131 123

cyB :: C
cyB Light = HSA.RGB 36 131 123
cyB Dark = HSA.RGB 58 169 159

blA :: C
blA Light = HSA.RGB 67 133 190
blA Dark = HSA.RGB 32 94 166

blB :: C
blB Light = HSA.RGB 32 94 166
blB Dark = HSA.RGB 67 133 190

puA :: C
puA Light = HSA.RGB 139 126 200
puA Dark = HSA.RGB 94 64 157

puB :: C
puB Light = HSA.RGB 94 64 157
puB Dark = HSA.RGB 139 126 200

maA :: C
maA Light = HSA.RGB 206 93 151
maA Dark = HSA.RGB 160 47 111

maB :: C
maB Light = HSA.RGB 160 47 111
maB Dark = HSA.RGB 206 93 151


pc = HSA.printColor


alpha :: Number -> HSA.Color -> HSA.Color
alpha n = case _ of
    HSA.RGB r g b -> HSA.RGBA r g b n
    HSA.RGBA r g b a -> HSA.RGBA r g b n
    color -> color


component :: Theme -> Number -> Number -> String
component t w h = "width:" <> show w <> "px; height: " <> show h <> "px; margin: 0; padding: 0; overflow: hidden; user-select: none; font-family: \"JetBrains Mono\", sans-serif; font-size: 10px; background-color: " <> pc (background t) <> ";"
graph = "" :: String
zoomBox = "margin: 5px; user-select: none;" :: String
breadcrumbs = "margin: 5px;" :: String
breadcrumbsWithSelection = "margin: 5px;" :: String
previewFocused = "opacity: 1.0;" :: String
previewBlurred = "opacity: 0.6;" :: String
previewNone = "" :: String
pinnedBox :: Number -> String
pinnedBox h = "position: relative; max-height: " <> show h <> "px; overflow: scroll"
pinnedLabel = "display: block; padding: 5px;" :: String
pinnedEdit = "position: absolute; right: 0; top: 0; display: block; padding: 5px; opacity: 0.5;" :: String
historyBox :: Theme -> String
historyBox theme = "user-select: none; padding: 10px; border: 1px solid rgb(190,190,190); margin: 5px 10px 5px 5px; background-color: " <> pc (background2 theme) <> ";"
textEditBox = "user-select: none;" :: String
foldRepBox :: { width :: Number, height :: Number } -> String
foldRepBox size = "position: relative; user-select: none; overflow: scroll; width: " <> show size.width <> "px; max-width: " <> show size.width <> "px; height: " <> show (size.height - 10.0) <> "px;" :: String
foldRepLine :: HSA.Color -> String
foldRepLine c = "display: block; background-color: " <> pc c <> ";"
foldRepColumn :: Int -> String
foldRepColumn n = "min-width: 60px; position: absolute; top: 0; left: " <> show (n * 100) <> "px;"
foldRepIndent = "display: inline-block; width: 10px; min-width: 10px; opacity: 0.3; color: lightgray;" :: String
jsonRepBox = "user-select: none;" :: String
button   = "cursor: pointer; pointer-events: all; padding: 2px 5px; margin: 0 2px; border-radius: 5px; border: 1px solid black; font-size: 9px; user-select: none; font-family: \"JetBrains Mono\", sans-serif;" :: String
pathBox = "display: inline-block;" :: String
pathWithGo = "" :: String
pathStep :: Boolean -> String
pathStep true  = "cursor: auto;    pointer-events: all; display: inline-block; padding: 2px 5px; margin: 2px 2px; border-radius: 5px; border: 1px solid rgb(230,230,230); font-size: 9px; user-select: none; font-family: \"JetBrains Mono\", sans-serif;"
pathStep false = "cursor: pointer; pointer-events: all; display: inline-block; padding: 2px 5px; margin: 2px 2px; border-radius: 5px; border: 1px solid rgb(90,90,90); font-size: 9px; user-select: none; font-family: \"JetBrains Mono\", sans-serif;"
zoomItem = "padding: 2px 5px;" :: String
hintsBox :: Theme -> String
hintsBox theme = "margin: 5px; max-width: 400px; padding: 2px 5px; border-radius: 5px; border: 1px solid rgb(190,190,190); background-color: " <> pc (background theme) <> ";"
hintsLine = "display: block;" :: String
value = "cursor: pointer; pointer-events: all;" :: String
edge  = "cursor: pointer; pointer-events: all;" :: String
previewBox = "pointer-events: none; display: block;" :: String
textarea :: Theme -> String
textarea theme = "font-family: \"JetBrains Mono\", sans-serif; font-size: 10px; border-radius: 6px; padding: 5px; background-color: " <> pc (background2 theme) <> ";"
pinBox = "" :: String