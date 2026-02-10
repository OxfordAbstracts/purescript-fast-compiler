module Webb.String.Helpers where

import Prelude

import Data.String (CodePoint)
import Data.String as String
import Webb.Array as Array


{- Helpers for working only with strings, even if this is more inefficient than working with codepoints. It can simply be useful in the common case, when efficiency isn't a priority, when quick conceptual match IS a priority.
-}

-- The the codepoint equivalent to the string?
codepointIs :: String -> CodePoint -> Boolean
codepointIs s cp = (String.fromCodePointArray [cp] == s)

takeEnd :: Int -> String -> String
takeEnd n string = let 
  cps = String.toCodePointArray string
  taken = Array.takeEnd n cps
  in String.fromCodePointArray taken
  
dropEnd :: Int -> String -> String
dropEnd n string = let 
  cps = String.toCodePointArray string
  dropped = Array.dropEnd n cps
  in String.fromCodePointArray dropped
