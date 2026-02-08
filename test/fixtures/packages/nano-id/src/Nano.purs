module Nano
  ( create
  , createDefault
  , createM
  )
  where

import Prelude

import Data.Maybe (Maybe(..), fromMaybe)
import Data.String (length)
import Data.String.Utils (charAt)
import Effect (Effect)
import Effect.Random (randomInt)

--Alphabet = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ_abcdefghijklmnopqrstuvwxyz-"
-- Get alphabet. Either default or specified by user
--let alphabet = Alphabet
-- Get random number between 0 and size of (string - 1) input to the function
alphabet :: String
alphabet = "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ_abcdefghijklmnopqrstuvwxyz-"

random_index :: String -> Effect Int
random_index s = randomInt 0 (length s-1)
-- get the element at the specified index.
-- this function is from Data.Char.Utils
get_elem_at :: String -> Int -> Maybe String
get_elem_at s i = charAt i s

-- Function for getting a random element from a string
get_random_elem_from_string :: String -> Effect (Maybe String)
get_random_elem_from_string s = do
  i <- random_index s
  el <- pure $ get_elem_at s i
  pure el

-- create :: Alphabet -> Size -> Effect (Maybe String)
-- create (AlphabetM ms) (SizeM mi) = create s i
--                 where s = AlphabetS (fromMaybe alphabet ms)
--                       i = SizeI (fromMaybe 21 mi)
-- create (AlphabetM ms) (SizeI i) = create s (SizeI i)
--                 where s = AlphabetS (fromMaybe alphabet ms)
-- create (AlphabetS s) (SizeM mi) = create (AlphabetS s) i
--                 where i = SizeI (fromMaybe 21 mi)
-- create (AlphabetS s) (SizeI i) | i > 0  = do
--                 mes <- get_random_elem_from_string s
--                 xs <- create (AlphabetS s) (SizeI (i-1))
--                 pure (mes <> xs)
--             | otherwise = pure Nothing

-- createDefault :: Effect (Maybe String)
-- createDefault = create (AlphabetM Nothing) (SizeM Nothing)

-- create generates random strings that comply with the NanoID algorithm.
-- Alternatively you can specify your own alphabet to generate the string from.
createM :: Maybe String -> Maybe Int -> Effect (Maybe String)
createM ms mi = create s i
                where s = fromMaybe alphabet ms
                      i = fromMaybe 21 mi
create :: String -> Int -> Effect (Maybe String)
create s i | i > 0  = do
                mes <- get_random_elem_from_string s
                xs <- create s (i-1)
                pure (mes <> xs)
            | otherwise = pure Nothing
createDefault :: Effect (Maybe String)
createDefault = createM Nothing Nothing
