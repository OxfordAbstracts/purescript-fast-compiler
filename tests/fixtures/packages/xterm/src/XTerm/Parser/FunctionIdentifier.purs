module XTerm.Parser.FunctionIdentifier where

import Data.Maybe (Maybe)

type FunctionIdentifier =
  { prefix :: Maybe String
  , intermediates :: Maybe String
  , final :: String
  }

