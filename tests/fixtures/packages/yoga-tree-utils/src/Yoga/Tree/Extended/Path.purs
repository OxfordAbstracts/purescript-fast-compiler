module Yoga.Tree.Extended.Path
    -- ( Path
    -- , Dir(..)
    -- , root
    -- , toArray, fromArray
    -- , depth
    -- , fill, fillDepths
    -- , find
    -- , with, traverse
    -- , startsWith, isNextFor
    -- , existsAt, posAt, lastPos
    -- , advance, up, advanceDir
    -- , safeAdvance, safeUp, safeDown, safeRight, safeLeft
    -- ) where
    where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Array (index, uncons, mapWithIndex, snoc, length, reverse, snoc, dropEnd, last) as Array
import Data.Tuple (fst, snd) as Tuple
import Data.Bifunctor (lmap)
import Data.Tuple.Nested ((/\), type (/\))
import Data.String (joinWith) as String
import Data.FoldableWithIndex (foldlWithIndex)

-- TODO: duplicates `Zipper.Loc` / depth first ?
-- TODO: if not, use `Zipper.Loc` with `Path`


import Yoga.Tree (Tree)
import Yoga.Tree.Extended (break, children, node, value) as YX


{-| Path is an array of positions of nodes required to be visited to reach some node. |-}
newtype Path = Path (Array Int)


instance Show Path where
    show (Path path) =
        case path of
            [] -> "*" -- "<root>"
            indices -> String.joinWith " :: " $ show <$> indices


derive instance Eq Path
derive instance Ord Path


{- Second path gets a new meaning, so it is better not to allow this

instance Monoid Path where
    mempty = root

instance Semigroup Path where
    append (Path pathA) (Path pathB) = Path $ pathA <> pathB
-}


{-| Root path. |-}
root :: Path
root = Path []


{-| Go deeper one level at the point with given index. |-}
advance :: Int -> Path -> Path
advance n (Path path) = Path $ Array.snoc path n


{-| Go up one level. |-}
up :: Path -> Path
up (Path path) = Path $ Array.dropEnd 1 path


{-| Convert path to an array. |-}
toArray :: Path -> Array Int
toArray (Path array) = array


{-| Create path from array. |-}
fromArray :: Array Int -> Path
fromArray = Path


{-| How deep is this path in the tree. |-}
depth :: Path -> Int
depth (Path arr) = Array.length arr


{-| Fill every value in this tree with its full path. |-}
fill :: forall a. Tree a -> Tree (Path /\ a)
fill = YX.break \a -> YX.node (Path [] /\ a) <<< Array.mapWithIndex (fill' [])
    where
        fill' path idx =
            let curPath = Array.snoc path idx
            in YX.break \a -> YX.node (Path curPath /\ a) <<< Array.mapWithIndex (fill' curPath)
    -- TODO: same as `traverse \path _ _ -> path`


{-| Find a deeper tree node by its given path. |-}
find :: forall a. Path -> Tree a -> Maybe (Tree a)
find (Path path) =
    if (Array.length path > 0)
    then flip find' path
    else Just
    where
        find' focus rempath =
            Array.uncons rempath >>=
                \{ head, tail } ->
                    Array.index (YX.children focus) head >>=
                        \child ->
                            if (Array.length tail > 0) then
                                find' child tail
                            else
                                Just child


{-| Call a function with the tree node at the given path. |-}
with :: forall a. Path -> (Tree a -> Tree a) -> Tree a -> Tree a
with (Path path) f =
    if (Array.length path > 0)
    then flip with' path
    else f
    where
        with' node rempath =
            case Array.uncons rempath of
                Just { head, tail } ->
                    YX.node (YX.value node)
                        $ Array.mapWithIndex (\idx child ->
                            if idx == head then
                                if (Array.length tail > 0) then
                                    with' child tail
                                else
                                    f child
                            else child
                        )
                        $ YX.children node
                Nothing -> node


{-| Walk around the complete tree, calling a function at every node with its path, value and children. |-}
traverse :: forall a b. (Path -> a -> Tree a -> b) -> Tree a -> Tree b
traverse f =
    traverse' []
    where
        traverse' path node =
            YX.break
                (\n ->
                    YX.node (f (Path path) n node)
                        <<< Array.mapWithIndex
                            (traverse' <<< Array.snoc path)
                )
                node


{-| Pair every value in the tree with how deep it is in this tree. |-}
fillDepths :: forall a. Tree a -> Tree (Int /\ a)
fillDepths = fill >>> map (lmap depth)


-- foldTraverse :: forall a b. (Path -> a -> Tree a -> b) -> Tree a -> b
-- foldTraverse = fill >>> foldl


{-| If first path contains full second path. They could be equal, but the second path couldn't be longer than the first one. Every path contains `root`. |-}
startsWith :: Path -> Path -> Boolean
startsWith first second =
    (depth second <= depth first) &&
    ( let
        firstArr = toArray first
        secondArr = toArray second
    in
        foldlWithIndex
            (\idx prev val -> prev && (Array.index firstArr idx == Just val))
            true
            secondArr
    )


{-| Value at given depth. |-}
posAt :: Path -> Int -> Maybe Int
posAt (Path pathArr) = Array.index pathArr


{-| Value at the last position. |-}
lastPos :: Path -> Maybe Int
lastPos path = posAt path $ depth path - 1


{-| If first path contains full second path, and the first path is exactly one level deeper than the second.
So if you would navigate at second path down (deeper), at the same index as the last position of the first path, then they would become equal. |-}
isNextFor :: Path -> Path -> Boolean
isNextFor first second =
    (depth first == depth second + 1) && startsWith first second


{-| Navigate deeper by given index but only if the index is in the bounds of how many children are accessibly by this path. |-}
safeAdvance :: forall a. Path -> Int -> Tree a -> Path
safeAdvance path n tree =
  case find path tree of
    Just subTree ->
        if n < (Array.length $ YX.children subTree) && n >= 0
            then path # advance n
            else path
    Nothing -> path


data Dir
    = Up -- one level up
    | Down -- one level deeper
    | Right -- next child
    | Left -- previous child


derive instance Eq Dir


{-| If the tree contains something at given path. |-}
existsAt :: forall a. Path -> Tree a -> Boolean
existsAt path tree =
    case find path tree of
        Just _ -> true
        Nothing -> false

{-| Safely go one level up to the root. |-}
safeUp :: forall a. Path -> Tree a -> Path
safeUp path = advanceDir path Up


{-| Safely go one level deeper, when possible. |-}
safeDown :: forall a. Path -> Tree a -> Path
safeDown path = advanceDir path Down


{-| Safely go to the next neigbouring child from the same parent. |-}
safeRight :: forall a. Path -> Tree a -> Path
safeRight path = advanceDir path Right


{-| Safely go to the previous neigbouring child from the same parent. |-}
safeLeft :: forall a. Path -> Tree a -> Path
safeLeft path = advanceDir path Left


{-| Safely (by checking bounds from this tree) advance this path one step in the requested direction:

    * `Up`: one level up to the root
    * `Down`: one level deeper, when possible
    * `Right`: to the next neigbouring child from the same parent
    * `Left` : to the previous neigbouring child from the same parent
|-}
advanceDir :: forall a. Path -> Dir -> Tree a -> Path
advanceDir path@(Path pathArr) Up tree =
    if (Array.length pathArr > 0)
        then
            if existsAt path tree
                then Path $ Array.dropEnd 1 pathArr
                else path
        else path
advanceDir path Down tree =
    safeAdvance path 0 tree
advanceDir path@(Path pathArr) Right tree =
    let
        parentPath = Path $ Array.dropEnd 1 pathArr
        mbLastPos = Array.last pathArr
    in
        case find parentPath tree of
            Just parentTree ->
                case mbLastPos of
                    Just theLastPos ->
                        if (Array.length $ YX.children parentTree) > 0
                        && (theLastPos + 1 < (Array.length $ YX.children parentTree))
                            then parentPath # advance (theLastPos + 1)
                            else path
                    Nothing -> path
            Nothing -> path
advanceDir path@(Path pathArr) Left tree =
    let
        parentPath = Path $ Array.dropEnd 1 pathArr
        mbLastPos = Array.last pathArr
    in
        case find parentPath tree of
            Just parentTree ->
                case mbLastPos of
                    Just theLastPos ->
                        if (Array.length $ YX.children parentTree) > 0
                        && (theLastPos - 1 >= 0)
                        && (theLastPos - 1 < (Array.length $ YX.children parentTree))
                            then parentPath # advance (theLastPos - 1)
                            else path
                    Nothing -> path
            Nothing -> path


{-| Convert to dashed text: `[ 0, 10, 12 ]` becomes `"0-10-12"`, `[]` becomes `"*"` |-}
dashed :: Path -> String
dashed (Path []) = "*"
dashed (Path trace) = String.joinWith "-" $ show <$> trace