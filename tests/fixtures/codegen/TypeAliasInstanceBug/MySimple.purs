-- Mirrors: type State s = StateT s Identity
-- MySimple is a type alias for MyTrans applied to a concrete type.
module MySimple where

import Prelude
import MyTrans
import Data.Newtype (class Newtype)

-- A simple Identity-like functor.
newtype MyId a = MyId a

derive instance newtypeMyId :: Newtype (MyId a) _

instance functorMyId :: Functor MyId where
  map f (MyId a) = MyId (f a)

-- Type alias: MySimple = MyTrans MyId
-- Mirrors: type State s = StateT s Identity
type MySimple = MyTrans MyId
