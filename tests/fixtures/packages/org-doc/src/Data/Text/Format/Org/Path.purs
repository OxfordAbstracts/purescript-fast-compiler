module Data.Text.Format.Org.Path where

import Prelude

import Data.Enum (class BoundedEnum)
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested ((/\), type (/\))
import Data.List (List, (:))
import Data.List (List(..)) as List
import Data.Array (cons, singleton, mapWithIndex) as Array
import Data.Foldable (foldr)
import Data.FoldableWithIndex (foldrWithIndex)

import Data.Text.Format.Org.Types (OrgFile, Block, Section) as T


data Axis a
    = Block a
    | Section a
    | Property a
    | Word a


derive instance Functor Axis


data Path a -- same as List (Axis a)
    = End
    | At (Axis a)
    | Next (Axis a) (Path a)


derive instance Functor Path


root :: forall a. Path a
root = End


infixr 6 cons as <:>


cons :: forall a. Axis a -> Path a -> Path a
cons = Next


toList :: forall a. Path a -> List (Axis a)
toList End = List.Nil
toList (At axis) = axis : List.Nil
toList (Next axis path) = axis : toList path


toArray :: forall a. Path a -> Array (Axis a)
toArray End = []
toArray (At axis) = Array.singleton axis
toArray (Next axis path) = Array.cons axis $ toArray path


instance Show a => Show (Axis a) where
    show = case _ of
        Block a -> "B" <> show a
        Section a -> "S" <> show a
        Property a -> "P" <> show a
        Word a -> "W" <> show a


instance Show a => Show (Path a) where
    show = case _ of
        End -> "*"
        At axis -> show axis
        Next axis path -> show axis <> " -> " <> show path


foldr :: forall a x. (Int -> Axis x -> a -> a) -> a -> Path x -> a
-- fold f a path = toArray path # Array.mapWithIndex f # foldr (const identity) a
foldr f a path = toArray path # foldrWithIndex f a


-- foldStep :: forall a x. BoundedEnum a => (Int -> Axis x -> a -> a) -> a -> Path x -> a
-- foldStep f a path = enumFromTo