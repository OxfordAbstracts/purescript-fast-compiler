module Yoga.Tree.Extended.Graph
    ( toGraph
    , toGraph'
    ) where

import Prelude

import Data.Graph (Graph)
import Data.Graph (fromMap) as Graph
import Data.Tuple (fst) as Tuple
import Data.Tuple.Nested ((/\))
import Data.Map (empty, insert) as Map
import Data.Array (toUnfoldable) as Array
import Data.Foldable (class Foldable, foldl)

import Yoga.Tree (Tree)
import Yoga.Tree.Extended (value, break) as Tree
import Yoga.Tree.Extended.Path (Path(..))
import Yoga.Tree.Extended.Path as Path


foldl' :: forall f a b. Foldable f => (b -> a -> b) -> f a -> b -> b
foldl' = flip <<< foldl


toGraph :: forall a. Tree a -> Graph Path a
toGraph = toGraph' Path.root


toGraph' :: forall a. Path -> Tree a -> Graph Path a
toGraph' (Path root) = Path.fill >>> Tree.break breakRoot >>> Graph.fromMap
    where
        breakNode theMap (path /\ a) xs =
            theMap
                # Map.insert
                    (alignWithRoot path)
                    (a /\
                        (Array.toUnfoldable
                             $  alignWithRoot
                            <$> Tuple.fst
                            <$> Tree.value
                            <$> xs
                        )
                    )
                # foldl' (Tree.break <<< breakNode) xs
        breakRoot =
            breakNode Map.empty
        alignWithRoot (Path path) =
            Path $ root <> path
