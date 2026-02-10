module DataMVC.Types.DataPath
  ( DataPath
  , DataPathSegment(..)
  , DataPathSegmentField(..)
  ) where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

--------------------------------------------------------------------------------
--- Types
--------------------------------------------------------------------------------

type DataPath = Array DataPathSegment

data DataPathSegment
  = SegCase String
  | SegField DataPathSegmentField

data DataPathSegmentField
  = SegStaticKey String
  | SegStaticIndex Int
  | SegDynamicKey String
  | SegDynamicIndex Int
  | SegVirtualKey String

--------------------------------------------------------------------------------
--- Instances
--------------------------------------------------------------------------------

derive instance Generic DataPathSegment _
derive instance Generic DataPathSegmentField _

instance Show DataPathSegment where
  show = genericShow

instance Show DataPathSegmentField where
  show = genericShow

derive instance Ord DataPathSegment
derive instance Ord DataPathSegmentField

derive instance Eq DataPathSegment
derive instance Eq DataPathSegmentField
