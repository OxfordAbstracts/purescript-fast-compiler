module TestRowsInInstance where

import Prelude

class MyTypeEquals a b | a -> b, b -> a where
  myCoerce :: a -> b
  myCoerceBack :: b -> a

instance myRefl :: MyTypeEquals a a where
  myCoerce = identity
  myCoerceBack = identity

newtype RecordNewtype = RecordNewtype { x :: String }

class OldStyleNewtype t a where
  myWrap :: a -> t
  myUnwrap :: t -> a

instance newtypeRecordNewtype ::
  MyTypeEquals inner { x :: String }
    => OldStyleNewtype RecordNewtype inner where
  myWrap = RecordNewtype <<< myCoerce
  myUnwrap (RecordNewtype rec) = myCoerceBack rec

test = (myUnwrap (RecordNewtype { x: "Done" })).x
-- TEST: "Done"
