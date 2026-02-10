module XTerm.UnicodeHandling where

import Data.Unit (Unit)
import Effect (Effect)


type UnicodeVersionProvider =
  { version :: String
  , wcwidth :: Int -> Int
  , charProperties :: Int -> Int -> Int
  }

data UnicodeHandling

foreign import registerVersionProvider :: UnicodeHandling -> UnicodeVersionProvider -> Effect Unit
foreign import registeredVersions :: UnicodeHandling -> Effect (Array String)
foreign import getActiveVersion :: UnicodeHandling -> Effect String
foreign import setActiveVersion :: UnicodeHandling -> String -> Effect Unit

