module DataMVC.Types.DataError
  ( DataError(..)
  , DataErrorCase(..)
  , DataResult
  , scopeError
  , scopeErrors
  , scopeOpt
  ) where

import Prelude

import Data.Array.NonEmpty (NonEmptyArray)
import Data.Bifunctor (lmap)
import Data.Either (Either)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import DataMVC.Types.DataPath (DataPathSegment, DataPath)

--------------------------------------------------------------------------------
--- Types
--------------------------------------------------------------------------------

type DataResult a = Either (NonEmptyArray DataError) a

data DataErrorCase
  = DataErrNotYetDefined
  | DataErrMsg String

data DataError = DataError DataPath DataErrorCase

--------------------------------------------------------------------------------
--- Constructors & Combinators
--------------------------------------------------------------------------------

scopeError :: DataPathSegment -> DataError -> DataError
scopeError seg (DataError path case_) = DataError ([ seg ] <> path) case_

scopeErrors :: DataPathSegment -> NonEmptyArray DataError -> NonEmptyArray DataError
scopeErrors seg = map (scopeError seg)

scopeOpt :: forall a. DataPathSegment -> DataResult a -> DataResult a
scopeOpt seg = lmap (scopeErrors seg)

--------------------------------------------------------------------------------
--- Instances
--------------------------------------------------------------------------------

derive instance Ord DataError

derive instance Eq DataError

derive instance Generic DataError _

derive instance Generic DataErrorCase _

instance Show DataError where
  show = genericShow

instance Show DataErrorCase where
  show = genericShow

derive instance Ord DataErrorCase
derive instance Eq DataErrorCase
