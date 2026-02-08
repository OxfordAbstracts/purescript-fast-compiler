module XTerm.Options.Logger where

import Data.Unit (Unit)
import Effect (Effect)
import Effect.Exception (Error)
import Foreign (Foreign)


type Logger = String -> Array Foreign -> Effect Unit
type ErrorLogger = Error -> Array Foreign -> Effect Unit

foreign import iLogger :: ILogger -> Foreign

type ILogger =
  { trace :: Logger
  , debug :: Logger
  , info :: Logger
  , warn :: Logger
  , error :: ErrorLogger
  }
