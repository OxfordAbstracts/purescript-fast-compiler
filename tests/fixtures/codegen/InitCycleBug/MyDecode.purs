-- Bug: instance name shadows an imported function.
-- The method body `myDecode = decodeVoid` should reference
-- the IMPORTED MyDecoders.decodeVoid, but the codegen treats it
-- as self-referential because the instance is also named `decodeVoid`.
--
-- In the package tests this manifests as:
--   decodeVoid was needed before it finished initializing
module MyDecode where

import MyDecoders

class MyDecode a where
  myDecode :: String -> MyResult a

-- A Void-like type — mirrors Data.Void
data MyVoid

-- Normal instance, no shadowing.
instance myDecodeString :: MyDecode String where
  myDecode = decodeString

-- Instance name `decodeVoid` shadows the imported `decodeVoid` function.
-- The method body should use the imported function, NOT self-reference.
-- Mirrors: instance decodeVoid :: DecodeJson Void where decodeJson = decodeVoid
instance decodeVoid :: MyDecode MyVoid where
  myDecode = decodeVoid
