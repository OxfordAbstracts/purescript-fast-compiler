module Yoga.Tree.Extended.Convert where

import Prelude
import Foreign (F, Foreign)

import Data.Newtype (class Newtype, unwrap)

import Control.Comonad.Cofree (head, tail)
import Control.Monad.Rec.Class (Step(..), tailRec)

import Data.Function (applyN)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Array (uncons, replicate, length) as Array
import Data.Tuple (fst, snd) as Tuple
import Data.Tuple.Nested ((/\), type (/\))
import Data.String (Pattern(..))
import Data.String (joinWith, split, length, takeWhile, drop) as String
import Data.Foldable (foldl)
import Data.FunctorWithIndex (mapWithIndex)
import Data.CodePoint.Unicode (isAlphaNum)

import Yoga.Tree (Tree, Forest)
import Yoga.Tree (appendChild, leaf)as Tree
import Yoga.Tree.Extended (node, children, break) as Tree
import Yoga.Tree.Extended.Path (Path)
import Yoga.Tree.Extended.Path (root, fill, with, advance, up, find, depth) as Path

import Yoga.JSON (E, class WriteForeign, class ReadForeign)
import Yoga.JSON (writeJSON, readJSON, writeImpl, readImpl) as Y


type LinesWithPaths = Array (Path /\ String)
type RenderStep = { current ∷ Forest (Path /\ String), drawn ∷ LinesWithPaths, level ∷ Int }


data Mode
    = Indent -- editable
    | Paths
    | Lines
    | Corners
    | Triangles
    | Dashes


derive instance Eq Mode
derive instance Ord Mode


data IsLast
    = NotLast
    | Last


newtype Depth = Depth Int
derive instance Newtype Depth _


toLines :: (Depth -> IsLast -> Path -> String) -> Tree String -> Array String
toLines prefixGen = toPathLines prefixGen >>> map Tuple.snd


toPathLines :: (Depth -> IsLast -> Path -> String) -> Tree String -> LinesWithPaths
toPathLines prefixGen tree =
    tailRec go { level: 0, drawn: [ head t ], current: (tail t) }
    where
    t :: Tree (Path /\ String)
    t = Path.fill tree
    go :: RenderStep -> Step RenderStep LinesWithPaths
    go x = case x { current = Array.uncons x.current } of
        { drawn: s, current: Nothing } -> Done s
        { level: l, drawn: s, current: Just { head: c, tail: cs } } ->
            let
                curPath = Tuple.fst $ head c :: Path
                curVal  = Tuple.snd $ head c :: String
                drawn =
                    prefixGen
                        (Depth $ Path.depth curPath)
                        (if (Array.length cs > 0) then NotLast else Last)
                        curPath
                    <> curVal
            in
                Loop { level: l, drawn: s <> pure (curPath /\ drawn) <> (tailRec go { level: l + 1, drawn: [], current: (tail c) }), current: cs }



modeToF :: Mode -> (Depth -> IsLast -> Path -> String)
modeToF = case _ of
    Indent ->    \(Depth n) _ _ -> String.joinWith "" $ Array.replicate n " "
    Paths ->     \_ _ path -> show path <> " // "
    Lines ->     \(Depth n) _ _ -> if n == 0 then "" else "|-" <> (String.joinWith "" $ Array.replicate (n - 1) "-")
    Triangles -> \(Depth n) _ _ -> if n == 0 then "" else ((String.joinWith "" $ Array.replicate (n - 1) "▹") <> "◦") -- ◦
    Dashes ->    \(Depth n) _ _->  if n == 0 then "" else "┊" <> (String.joinWith "" $ Array.replicate (n - 1) "┄")
    Corners ->   \(Depth n) isLast _ ->
        if n == 0
            then ""
            else
                ((String.joinWith "" $ Array.replicate (n - 1) "├")
                <> case isLast of
                        Last -> "└"
                        NotLast -> "├") -- ┠├└┡ ━



toString :: forall a. Mode -> (a -> String) -> Tree a -> String
toString mode convert = map convert >>> toLines (modeToF mode) >>> String.joinWith "\n"


showTree' :: forall a. Show a => Tree a -> String
showTree' = toString Indent show


type PreParseStep    = { index :: Int, level :: Int, str :: String }
type TreeParseStep a = { path :: Path, prevLevel :: Int, tree :: Tree (Maybe a) }


fromString :: forall a. (String -> Maybe a) -> String -> Tree (Maybe a)
fromString extract src =
    String.split (Pattern "\n") src
        <#> extractLevel
         #  mapWithIndex (/\)
        <#> addIndex
         #  Array.uncons
        <#> tryTree
        <#> _.tree
         #  fromMaybe emptyTree
    where

        foldF :: TreeParseStep a -> PreParseStep -> TreeParseStep a
        foldF { path, tree, prevLevel } { index, level, str } =

            if (level == prevLevel) || (prevLevel == 0 && level > prevLevel) then
                { path : path
                , tree : tree
                    # Path.with
                        path
                        (Tree.appendChild $ Tree.leaf $ extract str)
                , prevLevel : level
                }

            else if level > prevLevel then
                let
                    childIndex =
                        case Path.find path tree of
                            Just subTree -> (Array.length $ Tree.children subTree) - 1
                            Nothing -> 0
                    nextPath = path # Path.advance childIndex
                in
                { path : nextPath
                , tree : tree
                    # Path.with
                        nextPath
                        (Tree.appendChild $ Tree.leaf $ extract str)
                , prevLevel : level
                }

            else -- level < prevLevel
                let
                    nextPath = path # applyN Path.up (prevLevel - level)
                in
                { path : nextPath
                , tree : tree
                    # Path.with
                        nextPath
                        (Tree.appendChild $ Tree.leaf $ extract str)
                , prevLevel : level
                }

        emptyTree :: Tree (Maybe a)
        emptyTree = Tree.leaf Nothing

        tryTree :: { head :: PreParseStep, tail :: Array PreParseStep } -> TreeParseStep a
        tryTree { head, tail } =
            if (head.index == 0) && (head.level == 0)
                then foldl foldF ({ path : Path.root, tree : Tree.leaf $ extract head.str, prevLevel : 0 }) tail
                else { path : Path.root, tree : emptyTree, prevLevel : 0 }

        addIndex :: Int /\ { level :: Int, str :: String } -> PreParseStep
        addIndex (index /\ { level, str }) = { level, str, index }

        extractLevel :: String -> { level :: Int, str :: String }
        extractLevel source =
            let
                prefix = String.takeWhile (not <<< isAlphaNum) source
                level = String.length prefix
                remainder = String.drop level source
            in { level, str : remainder }


newtype JSONTree a = JSONTree (Tree a)

derive instance Newtype (JSONTree a) _


type JSONRec a = { v :: a, cs :: Array (JSONTree a) }


instance WriteForeign a => WriteForeign (JSONTree a) where
    writeImpl :: JSONTree a -> Foreign
    writeImpl (JSONTree tree) =
        Tree.break breakF tree
        where
            breakF :: a -> Array (Tree a) -> Foreign
            breakF a cs =
                Y.writeImpl
                    { v  : Y.writeImpl a
                    , cs : Y.writeImpl $ JSONTree <$> cs
                    }


instance ReadForeign a => ReadForeign (JSONTree a) where
    readImpl :: Foreign -> F (JSONTree a)
    readImpl f = do
        (rec :: (JSONRec a)) <- Y.readImpl f
        pure $ JSONTree $ Tree.node rec.v $ unwrap <$> rec.cs


writeJSON :: forall a. WriteForeign a => Tree a -> String
writeJSON = JSONTree >>> Y.writeJSON


readJSON :: forall a. ReadForeign a => String -> E (Tree a)
readJSON str = unwrap <$> (Y.readJSON str :: E (JSONTree a))