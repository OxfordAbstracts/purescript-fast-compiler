module XTerm.Options.WindowOptions where

import Data.Options (Option, opt)

data WindowOptions

type WindowOption = Option WindowOptions

restoreWin :: WindowOption Boolean
restoreWin = opt "restoreWin"

minimizeWin :: WindowOption Boolean
minimizeWin = opt "minimizeWin"

setWinPosition :: WindowOption Boolean
setWinPosition = opt "setWinPosition"

setWinSizePixels :: WindowOption Boolean
setWinSizePixels = opt "setWinSizePixels"

raiseWin :: WindowOption Boolean
raiseWin = opt "raiseWin"

lowerWin :: WindowOption Boolean
lowerWin = opt "lowerWin"

refreshWin :: WindowOption Boolean
refreshWin = opt "refreshWin"

setWinSizeChars :: WindowOption Boolean
setWinSizeChars = opt "setWinSizeChars"

maximizeWin :: WindowOption Boolean
maximizeWin = opt "maximizeWin"

fullscreenWin :: WindowOption Boolean
fullscreenWin = opt "fullscreenWin"

getWinState :: WindowOption Boolean
getWinState = opt "getWinState"

getWinPosition :: WindowOption Boolean
getWinPosition = opt "getWinPosition"

getWinSizePixels :: WindowOption Boolean
getWinSizePixels = opt "getWinSizePixels"

getScreenSizePixels :: WindowOption Boolean
getScreenSizePixels = opt "getScreenSizePixels"

getCellSizePixels :: WindowOption Boolean
getCellSizePixels = opt "getCellSizePixels"

getWinSizeChars :: WindowOption Boolean
getWinSizeChars = opt "getWinSizeChars"

getScreenSizeChars :: WindowOption Boolean
getScreenSizeChars = opt "getScreenSizeChars"

getIconTitle :: WindowOption Boolean
getIconTitle = opt "getIconTitle"

getWinTitle :: WindowOption Boolean
getWinTitle = opt "getWinTitle"

pushTitle :: WindowOption Boolean
pushTitle = opt "pushTitle"

popTitle :: WindowOption Boolean
popTitle = opt "popTitle"

setWinLines :: WindowOption Boolean
setWinLines = opt "setWinLines"


