module XTerm.Options.WindowsPty where

import Control.Category ((<<<))
import Data.Generic.Rep (class Generic)
import Data.Op (Op(..))
import Data.Options (Option, Options(..), opt)
import Data.Show (class Show, show)
import Data.Show.Generic (genericShow)
import Data.String (toLower)
import Data.Tuple (Tuple(..))
import Foreign (unsafeToForeign)

data WindowsPty

data Backend = ConPty | WinPty

derive instance Generic Backend _

instance Show Backend where
  show = genericShow

backendString :: Backend -> String
backendString = toLower <<< show

backend :: Option WindowsPty Backend
backend = Op (\v -> Options [ Tuple "backend" (unsafeToForeign (backendString v)) ])

buildNumber :: Option WindowsPty Int
buildNumber = opt "buildNumber"

