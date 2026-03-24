-- Bug: when resolving Functor for MySimple (a type alias for MyTrans MyId),
-- the codegen should emit functorMyTrans(functorMyId) but instead emits
-- the non-existent functorMySimple.
--
-- Mirrors the real bug: type Gen a = Gen (State GenState a) with
--   derive newtype instance functorGen :: Functor Gen
-- where type State s = StateT s Identity, so Functor Gen should resolve
-- to functorStateT(functorIdentity) but resolves to functorState (undefined).
--
-- In the package tests this manifests as:
--   functorState is not defined
module TestTypeAlias where

import Prelude
import MyTrans
import MySimple
import Data.Newtype (class Newtype)

-- A newtype wrapping the type alias, with a derived Functor.
-- This mirrors: newtype Gen a = Gen (State GenState a)
--               derive newtype instance functorGen :: Functor Gen
newtype MyWrapper a = MyWrapper (MySimple a)

derive instance newtypeMyWrapper :: Newtype (MyWrapper a) _

-- Deriving Functor through the newtype.
-- Should resolve to functorMyTrans(functorMyId), NOT functorMySimple.
derive newtype instance functorMyWrapper :: Functor MyWrapper

test = case map (\x -> x <> " world") (MyWrapper (MyTrans (MyId "hello")) :: MyWrapper String) of
  MyWrapper (MyTrans (MyId s)) -> s

-- TEST: "hello world"
