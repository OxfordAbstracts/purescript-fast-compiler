module XTerm.Link
  ( LinkAction
  , LinkOptions
  , LinkOption
  , Link(..)
  , LinkDecorations(..) 
  , ILink
  , makeLink
  , decorations
  , hover
  , leave
  , onDispose
  ) where

import Data.Options (Option, Options, opt, options)
import Data.Unit (Unit)
import Effect (Effect)
import Foreign (Foreign)
import Web.UIEvent.MouseEvent (MouseEvent)
import XTerm.Buffer (BufferRange)

type LinkAction = MouseEvent -> String -> Effect Unit

data LinkOptions

type LinkOption = Option LinkOptions

type Link =
  { range :: BufferRange
  , text :: String
  , activate :: LinkAction
  , linkOptions :: Options LinkOptions 
  }

type LinkDecorations =
  { pointerCursor :: Boolean
  , underline :: Boolean
  }

data ILink

foreign import _makeLink :: BufferRange -> String -> LinkAction -> Foreign -> ILink

makeLink :: Link -> ILink
makeLink { range, text, activate, linkOptions } = _makeLink range text activate (options linkOptions)

decorations :: LinkOption LinkDecorations
decorations = opt "decorations"

hover :: LinkOption LinkAction
hover = opt "hover"

leave :: LinkOption LinkAction
leave = opt "leave"

onDispose :: LinkOption (Effect Unit)
onDispose = opt "dispose"

