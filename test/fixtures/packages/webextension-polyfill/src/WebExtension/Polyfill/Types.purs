module WebExtension.Polyfill.Types where

import Prelude
import Data.Newtype (class Newtype)

newtype StorageKey = StorageKey String

derive instance newtypeStorageKey ∷ Newtype StorageKey _
derive newtype instance eqStorageKey ∷ Eq StorageKey
derive newtype instance ordStorageKey ∷ Ord StorageKey
