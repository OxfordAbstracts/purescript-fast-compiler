module XTerm.Options where


import CSS (FontWeight(..), Prefixed(..), Value(..))
import Control.Category ((<<<))
import Data.Generic.Rep (class Generic)
import Data.Op (Op(..))
import Data.Options (Option, Options(..), opt, options)
import Data.Show (class Show, show)
import Data.Show.Generic (genericShow)
import Data.String (toLower)
import Data.Tuple (Tuple(..))
import Data.Unit (Unit)
import Effect (Effect)
import Foreign (unsafeFromForeign, unsafeToForeign)
import XTerm.Options.LinkHandler (LinkHandler, makeLinkHandler)
import XTerm.Options.Logger (ILogger, iLogger)
import XTerm.Options.Theme (Theme)
import XTerm.Options.WindowOptions (WindowOptions)
import XTerm.Options.WindowsPty (WindowsPty)

data TerminalInitOnlyOptions

cols :: Option TerminalInitOnlyOptions Int
cols = opt "cols"

rows :: Option TerminalInitOnlyOptions Int
rows = opt "rows"


data TerminalOptions

terminalOptions :: Options TerminalOptions -> TerminalOptions
terminalOptions = unsafeFromForeign <<< options

type TerminalOption = Option TerminalOptions

allowProposedApi :: TerminalOption Boolean
allowProposedApi = opt "allowProposedApi"

allowTransparency :: TerminalOption Boolean
allowTransparency = opt "allowTransparency"

altClickMoveCursor :: TerminalOption Boolean
altClickMoveCursor = opt "altClickRemoveCursor"

convertEol :: TerminalOption Boolean
convertEol = opt "covertEol"

cursorBlink :: TerminalOption Boolean
cursorBlink = opt "cursorBlink"

foreign import getCursorBlink :: TerminalOptions -> Effect Boolean
foreign import setCursorBlink :: TerminalOptions -> Boolean -> Effect Unit

data CursorStyle = Block | Underline | Bar

derive instance Generic CursorStyle _

instance Show CursorStyle where
  show = genericShow

cursorStyleOptionString :: CursorStyle -> String
cursorStyleOptionString = toLower <<< show

cursorStyle :: TerminalOption CursorStyle
cursorStyle = Op (\v -> Options [ Tuple "cursorStyle" (unsafeToForeign (cursorStyleOptionString v)) ])

cursorWidth :: TerminalOption Int
cursorWidth = opt "cursorWidth"

data CursorInteractiveStyle = CursorStyle CursorStyle | Outline | None

derive instance Generic CursorInteractiveStyle _

instance Show CursorInteractiveStyle where
  show = genericShow

cursorInteractiveStyleOptionString :: CursorInteractiveStyle -> String
cursorInteractiveStyleOptionString None = "none"
cursorInteractiveStyleOptionString Outline = "outline"
cursorInteractiveStyleOptionString (CursorStyle s) = cursorStyleOptionString s

cursorInteractiveStyle :: TerminalOption CursorInteractiveStyle
cursorInteractiveStyle = 
  Op (\v -> Options [ Tuple "cursorInteractiveStyle" (unsafeToForeign (cursorInteractiveStyleOptionString v)) ])

customGlyphs :: TerminalOption Boolean
customGlyphs = opt "customGlyphs"

disableStdin :: TerminalOption Boolean
disableStdin = opt "disableStdin"

drawBoldTextInBrightColors :: TerminalOption Boolean
drawBoldTextInBrightColors = opt "drawBoldTextInBrightColors"

-- 'none' | 'alt' | 'ctrl' | 'shift'
fastScrollModifier :: TerminalOption String
fastScrollModifier = opt "fastScrollModifier"

fastScrollSensitivity :: TerminalOption Number
fastScrollSensitivity = opt "fastScrollSensitivity"

fontSize :: TerminalOption Number
fontSize = opt "fontSize"

fontFamily :: TerminalOption String
fontFamily = opt "fontFamily"

foreign import getFontFamily :: TerminalOptions -> Effect String
foreign import setFontFamily :: TerminalOptions -> String -> Effect Unit

fopt :: forall opt . String -> Op (Options opt) FontWeight
fopt = Op <<< fontWeightOpt
  where
    fontWeightOpt k (FontWeight (Value (Plain s))) = Options [ Tuple k (unsafeToForeign s) ]
    fontWeightOpt k _ = Options [ Tuple k (unsafeToForeign "normal") ]

fontWeight :: TerminalOption FontWeight
fontWeight = fopt "fontWeight"

fontWeightBold :: TerminalOption FontWeight
fontWeightBold = fopt "fontWeightBold"

ignoreBracketedPasteMode :: TerminalOption Boolean
ignoreBracketedPasteMode = opt "ignoreBracketedPasteMode"

letterSpacing :: TerminalOption Int
letterSpacing = opt "letterSpacing"

lineHeight :: TerminalOption Int
lineHeight = opt "lineHeight"

linkHandler :: TerminalOption LinkHandler
linkHandler = Op (\{ activate, handlerOptions } ->
                   Options [ Tuple "linkHandler" (makeLinkHandler activate (options handlerOptions)) ]) 

data LogLevel = Trace | Debug | Info | Warn | Error | Off

derive instance Generic LogLevel _

instance Show LogLevel where
  show = genericShow

logLevelString :: LogLevel -> String
logLevelString = toLower <<< show

logLevel :: TerminalOption LogLevel
logLevel = Op (\v -> Options [ Tuple "logLevel" (unsafeToForeign (logLevelString v)) ])

logger :: TerminalOption ILogger
logger = Op (\l -> Options [ Tuple "logger" (iLogger l) ])

macOptionIsMeta :: TerminalOption Boolean
macOptionIsMeta = opt "macOptionIsMeta"

macOptionClickForcesSelection :: TerminalOption Boolean
macOptionClickForcesSelection = opt "macOptionClickForcesSelection"

minimumContrastRatio :: TerminalOption Number
minimumContrastRatio = opt "minimumContrastRatio"

rightClickSelectsWord :: TerminalOption Boolean
rightClickSelectsWord = opt "rightClickSelectsWord"

screenReaderMode :: TerminalOption Boolean
screenReaderMode = opt "screenReaderMode"

scrollback :: TerminalOption Int
scrollback = opt "scrollback"

scrollOnUserInput :: TerminalOption Boolean
scrollOnUserInput = opt "scrollOnUserInput"

scrollSensitivity :: TerminalOption Number
scrollSensitivity = opt "scrollSensitivity"

smoothScrollDuration :: TerminalOption Number
smoothScrollDuration = opt "smoothScrollDuration"

tabStopWidth :: TerminalOption Int
tabStopWidth = opt "tabStopWidth"

theme :: TerminalOption (Options Theme)
theme = Op (\v -> Options [ Tuple "theme" (options v) ])

windowsMode :: TerminalOption Boolean
windowsMode = opt "windowsMode"


windowsPty :: TerminalOption (Options WindowsPty)
windowsPty = Op (\v -> Options [ Tuple "windowsPty" (options v) ])

wordSeparator :: TerminalOption String
wordSeparator = opt "wordSeparator"


windowOptions :: TerminalOption (Options WindowOptions)
windowOptions = Op (\v -> Options [ Tuple "windowOptions" (options v) ])

overviewRulerWidth :: TerminalOption Int
overviewRulerWidth = opt "overviewRulerWidth"


