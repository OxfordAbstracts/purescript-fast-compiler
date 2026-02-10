module Webb.Channel.Data.Id where

import Prelude

import Data.Int (rem)
import Data.Newtype (class Newtype, unwrap, wrap, modify)




newtype Id = I Int

derive newtype instance Eq Id
derive newtype instance Ord Id
derive newtype instance Show Id
derive instance Newtype Id _

fromInt :: Int -> Id
fromInt = wrap

toInt :: Id -> Int
toInt = unwrap

next :: Id -> Id
next = modify $ \i -> rem (i + 1) 10000

prev :: Id -> Id
prev = modify $ \i -> rem (i - 1) 10000

initial :: Id
initial = wrap 0