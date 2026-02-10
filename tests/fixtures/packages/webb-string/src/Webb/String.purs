module Webb.String 
( module P
, WString
)
where

import Prelude

import Data.String as P
import Webb.String.Helpers as P
import Webb.String.TrimMargin (trimMargin) as P

{- Functions for working with strings. -}


type WString = String