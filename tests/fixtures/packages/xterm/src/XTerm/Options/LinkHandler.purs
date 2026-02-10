module XTerm.Options.LinkHandler where

import Data.Options (Option, Options, opt)
import Data.Unit (Unit)
import Effect (Effect)
import Foreign (Foreign)
import Web.UIEvent.MouseEvent (MouseEvent)
import XTerm.Buffer (BufferRange)


type LinkHandler = 
  { activate :: HandleLink
  , handlerOptions :: Options LinkHandlerOptions
  }

data LinkHandlerOptions

foreign import makeLinkHandler :: HandleLink -> Foreign -> Foreign

type HandleLink = MouseEvent -> String -> BufferRange -> Effect Unit

hover :: Option LinkHandlerOptions HandleLink 
hover = opt "hover"

leave :: Option LinkHandlerOptions HandleLink 
leave = opt "leave"

allowNonHttpProtocols :: Option LinkHandlerOptions Boolean
allowNonHttpProtocols = opt "allowNonHttpProtocols"



