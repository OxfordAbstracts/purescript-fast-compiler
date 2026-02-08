module Webb.Channel.Data.CMaybe where

import Prelude

import Data.Foldable (class Foldable, foldMapDefaultL, foldrDefault)


{- The CMaybe data type is separate from Maybe, to make merging them 
  impossible, because CMaybe intends to indicate whether the Channel
  _closed_, to prevent infinite loops.
-}

data CMaybe a = Closed | Open a

instance Functor CMaybe where
  map f (Open a) = Open (f a)
  map _ Closed = Closed
  
instance Foldable CMaybe where
  foldl f acc (Open val) = f acc val
  foldl _ acc (Closed) = acc
  foldr f acc value = foldrDefault f acc value
  foldMap = foldMapDefaultL
  
isClosed :: forall a. CMaybe a -> Boolean
isClosed = case _ of
  Closed -> true
  Open _ -> false

isOpen :: forall a. CMaybe a -> Boolean
isOpen = case _ of
  Closed -> false
  Open _ -> true