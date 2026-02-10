module Test.MVC.TestTypes where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)

data M1 = M1 | M1' | M1''
data M2 = M2 | M2' | M2''
data M3 = M3 | M3' | M3''

data S1 = S1 | S1' | S1''
data S2 = S2 | S2' | S2''
data S3 = S3 | S3' | S3''

data T1 = T1 | T1' | T1''
data T2 = T2 | T2' | T2''
data T3 = T3 | T3' | T3''

data HTML :: Type -> Type
data HTML a = HTML

-----------------------------------------------------------
--- Instances
-----------------------------------------------------------

derive instance Functor HTML

derive instance Generic M1 _
derive instance Generic M2 _
derive instance Generic M3 _

derive instance Generic S1 _
derive instance Generic S2 _
derive instance Generic S3 _

derive instance Generic T1 _
derive instance Generic T2 _
derive instance Generic T3 _

derive instance Eq M1
derive instance Eq M2
derive instance Eq M3

derive instance Eq S1
derive instance Eq S2
derive instance Eq S3

derive instance Eq T1
derive instance Eq T2
derive instance Eq T3

instance Show M1 where
  show = genericShow

instance Show M2 where
  show = genericShow

instance Show M3 where
  show = genericShow

instance Show S1 where
  show = genericShow

instance Show S2 where
  show = genericShow

instance Show S3 where
  show = genericShow

instance Show T1 where
  show = genericShow

instance Show T2 where
  show = genericShow

instance Show T3 where
  show = genericShow

