module Webb.Mutex.Data.Mutex.Id where

import Prelude

import Data.Int (rem)
import Data.Newtype (class Newtype, modify, unwrap, wrap)




newtype Id = I Int


derive newtype instance Eq Id
derive newtype instance Ord Id
derive newtype instance Show Id
derive instance Newtype Id _

toInt :: Id -> Int
toInt i = unwrap i

fromInt :: Int -> Id
fromInt i = wrap i

next :: Id -> Id
next = modify $ inc
  where
  inc id = rem (id + 1) 100000

prev :: Id -> Id
prev = modify $ dec
  where
  dec id = rem (id - 1) 100000
  
initial :: Id 
initial = wrap 0