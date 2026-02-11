module Router.Method
  ( Method(..)
  , fromString
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Data.String as String

data Method
  = GET
  | POST
  | PUT
  | DELETE
  | PATCH
  | HEAD
  | OPTIONS
  | TRACE
  | CONNECT

derive instance eqMethod :: Eq Method

derive instance ordMethod :: Ord Method

fromString :: String -> Maybe Method
fromString s =
  let
    normalized = String.toUpper s
  in
    case normalized of
      "GET" -> Just GET
      "POST" -> Just POST
      "PUT" -> Just PUT
      "DELETE" -> Just DELETE
      "PATCH" -> Just PATCH
      "HEAD" -> Just HEAD
      "OPTIONS" -> Just OPTIONS
      "TRACE" -> Just TRACE
      "CONNECT" -> Just CONNECT
      _ -> Nothing
