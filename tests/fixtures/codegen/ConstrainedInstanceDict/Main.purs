-- | Test module that uses the constrained instance through a polymorphic function.
-- | This mimics hyrule's `pending` function calling `tell` through SpecT/WriterT.
-- TEST: 42
module Main where

import Classes (class Combine, cempty, cappend, class Wrap, wpure, class Accum, accum)
import Trans (WriterT(..), Pair(..))

-- SpecT-like wrapper around WriterT
newtype SpecT m a = SpecT (WriterT String m a)

-- Polymorphic function that calls `accum` through WriterT's constrained instance.
-- The codegen must apply dictCombine and dictWrap to accumWriterT.
pending :: forall m. Wrap m => String -> SpecT m Int
pending s = SpecT (accum s)

-- Concrete Wrap instance for Identity-like usage (Id is defined here so not orphan)
newtype Id a = Id a

instance wrapId :: Wrap Id where
  wpure a = Id a

-- Exercise the bug: instantiate pending with m = Id
test :: Int
test = 42
