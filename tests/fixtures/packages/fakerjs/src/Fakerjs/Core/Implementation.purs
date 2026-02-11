module Fakerjs.Core.Implementation where

import Fakerjs.Core.Types

import Data.Array.NonEmpty (NonEmptyArray)
import Data.Function.Uncurried (Fn2, runFn2)
import Data.Maybe (Maybe)
import Data.Nullable (Nullable)
import Data.Nullable as Nullable

foreign import makeFakerImpl :: Fn2 (NonEmptyArray FakerLocale) (Nullable Int) Faker

makeFaker :: NonEmptyArray FakerLocale -> Maybe Int -> Faker
makeFaker array mseed = runFn2 makeFakerImpl array (Nullable.toNullable mseed)
