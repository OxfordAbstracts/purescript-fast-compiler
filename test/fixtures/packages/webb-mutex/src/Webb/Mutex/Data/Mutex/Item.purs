module Webb.Mutex.Data.Mutex.Item where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Newtype (class Newtype, unwrap, wrap)
import Webb.Mutex.Data.Mutex.Id (Id)
import Webb.Result (Result)


newtype Item = I Item_

instance Eq Item where
  eq a1 a2 = abbr a1 == abbr a2
instance Ord Item where
  compare a1 a2 = compare (abbr a1) (abbr a2)

derive newtype instance Show Item
derive instance Newtype Item _

type Tag = Id

type Item_ = 
  { tag :: Tag
  , name :: Maybe String
  , result :: Result Unit
  }

type Abbr = 
  { tag :: Tag
  , name :: Maybe String
  }
  
newItem :: Tag -> Maybe String -> Result Unit -> Item
newItem tag' name' result' = wrap 
  { tag: tag'
  , name: name'
  , result: result' 
  }

abbr :: Item -> Abbr
abbr i = let 
  item = unwrap i
  in { tag: item.tag, name: item.name }
  
result :: Item -> Result Unit
result = unwrap >>> _.result

tag :: Item -> Tag
tag = unwrap >>> _.tag

name :: Item -> Maybe String
name = unwrap >>> _.name

hasTag :: Tag -> Item -> Boolean
hasTag t item = tag item == t

hasName :: String -> Item -> Boolean
hasName n item = name item == Just n