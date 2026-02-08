module Test.Main where

import Prelude
import Foreign (renderForeignError)

import Data.String (toUpper, joinWith) as String
import Data.Array (length, fromFoldable) as Array
import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.Tuple.Nested ((/\), type (/\))
import Data.Int (fromString) as Int

import Effect (Effect)
import Effect.Aff (launchAff_)

import Control.Comonad.Cofree ((:<))
import Control.Monad.Error.Class (class MonadThrow)
import Effect.Exception (Error) as Ex


import Test.Spec (describe, it, itOnly)
import Test.Spec.Assertions (fail, shouldEqual)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner (runSpec)

import Yoga.Tree (appendChild) as Tree
import Yoga.Tree.Extended (Tree, (:<~))
import Yoga.Tree.Extended (node, leaf, set, update, children, flatten, edges, alter, break, regroup) as Tree
import Yoga.Tree.Extended.Path (Path(..))
import Yoga.Tree.Extended.Path (with, traverse, find, root, advance, up, toArray, startsWith, isNextFor, safeAdvance, advanceDir, dashed, Dir(..)) as Path
import Yoga.Tree.Extended.Convert (Mode(..), fromString, readJSON, toString, writeJSON) as Convert
import Yoga.JSON (E)


ql = Tree.leaf


main :: Effect Unit
main = launchAff_ $ runSpec [consoleReporter] do
  describe "purescript-yoga-tree-utils" $ do

    describe "basics" $ do
      it "root is empty path" $ do
        Path.toArray Path.root `shouldEqual` []
      it "advancing works" $ do
        Path.toArray (Path.root # Path.advance 3 # Path.advance 3 # Path.advance 7)
        `shouldEqual`
        [ 3, 3, 7 ]
      it "going up works" $ do
        Path.toArray (Path.root # Path.advance 7 # Path.advance 4 # Path.advance 3 # Path.up)
        `shouldEqual`
        [ 7, 4 ]
      it "flatten works" $ do
        (Tree.flatten $ 'a' :< [ ql 'b', ql 'c', 'd' :<~ [ '1', '2', '3' ], ql 'e' ])
        `shouldEqual`
        [ 'a', 'b', 'c', 'd', '1', '2', '3', 'e' ]

    describe "`with`+`set`" $ do

      it "`with` : `set` on the root path" $
        (Path.with (Path []) (Tree.set 'b') $ ql 'a')
        `compareTrees`
        (ql 'b')
      it "`with` : `set` with one of the children" $
        (Path.with (Path [2]) (Tree.set 'x')
          $ 'a' :<~ [ 'b', 'c', 'd', 'e' ]
        )
        `compareTrees`
        ('a' :<~ [ 'b', 'c', 'x', 'e' ])
      it "`with` : `set` with the children that is an empty node" $
        (Path.with (Path [2]) (Tree.set 'x')
          $ 'a' :< [ ql 'b', ql 'c', 'd' :< [], ql 'e' ]
        )
        `compareTrees`
        ('a' :< [ ql 'b', ql 'c', 'x' :< [], ql 'e' ])
      it "`with` : `set` with the children that is a node with leafs" $
        (Path.with (Path [2]) (Tree.set 'x')
          $ 'a' :< [ ql 'b', ql 'c', 'd' :<~ [ '1', '2', '3' ], ql 'e' ]
        )
        `compareTrees`
        ('a' :< [ ql 'b', ql 'c', 'x' :<~ [ '1', '2', '3' ], ql 'e' ])
      it "`with` : `set` with the children on a deeper level" $
        (Path.with (Path [2, 0]) (Tree.set 'x')
          $ 'a' :< [ ql 'b', ql 'c', 'd' :<~ [ '1', '2', '3' ], ql 'e' ]
        )
        `compareTrees`
        ('a' :< [ ql 'b', ql 'c', 'd' :<~ [ 'x', '2', '3' ], ql 'e' ])
      it "`with` : `set` when child doesn't exist" $
        (Path.with (Path [2, 7]) (Tree.set 'x')
          $ 'a' :< [ ql 'b', ql 'c', 'd' :<~ [ '1', '2', '3' ], ql 'e' ]
        )
        `compareTrees`
        ('a' :< [ ql 'b', ql 'c', 'd' :<~ [ '1', '2', '3' ], ql 'e' ])

    describe "`with`+`update`" $ do

      it "`with` : `update` on the root path" $
        (Path.with (Path []) (Tree.update String.toUpper) $ ql "a")
        `compareTrees`
        (ql "A")
      it "`with` : `update` with one of the children" $
        (Path.with (Path [2]) (Tree.update String.toUpper)
          $ "a" :<~ [ "b", "c", "d", "e" ]
        )
        `compareTrees`
        ("a" :<~ [ "b", "c", "D", "e" ])
      it "`with` : `update` with the children that is an empty node" $ do
        (Path.with (Path [2]) (Tree.update String.toUpper)
          $ "a" :< [ ql "b", ql "c", "d" :< [], ql "e" ]
        )
        `compareTrees`
        ("a" :< [ ql "b", ql "c", "D" :< [], ql "e" ])
      it "`with` : `update` with the children that is a node with leafs" $
        (Path.with (Path [2]) (Tree.update String.toUpper)
          $ "a" :< [ ql "b", ql "c", "d" :<~ [ "q", "r", "s" ], ql "e" ]
        )
        `compareTrees`
        ("a" :< [ ql "b", ql "c", "D" :<~ [ "q", "r", "s" ], ql "e" ])
      it "`with` : `update` with the children on a deeper level" $
        (Path.with (Path [2, 0]) (Tree.update String.toUpper)
          $ "a" :< [ ql "b", ql "c", "d" :<~ [ "q", "r", "s" ], ql "e" ]
        )
        `compareTrees`
        ("a" :< [ ql "b", ql "c", "d" :<~ [ "Q", "r", "s" ], ql "e" ])
      it "`with` : `update` when child doesn't exist" $
        (Path.with (Path [2, 7]) (Tree.update String.toUpper)
          $ "a" :< [ ql "b", ql "c", "d" :<~ [ "q", "r", "s" ], ql "e" ]
        )
        `compareTrees`
        ("a" :< [ ql "b", ql "c", "d" :<~ [ "q", "r", "s" ], ql "e" ])


    describe "`with`+`appendChild`" $ do

      it "`with`: properly appends child at root" $
        (Path.with (Path []) (Tree.appendChild $ ql "b") $ ql "a")
        `compareTrees`
        ("a" :<~ [ "b" ])

      it "`with`: properly appends child at root that already has children" $
        (Path.with (Path []) (Tree.appendChild $ ql "c") $ "a" :<~ [ "b" ])
        `compareTrees`
        ("a" :<~ [ "b", "c" ])

      it "`with`: properly appends child at some node" $
        (Path.with (Path [ 0 ]) (Tree.appendChild $ ql "c") $ "a" :<~ [ "b" ])
        `compareTrees`
        ("a" :< [ "b" :<~ [ "c" ] ])

      it "`with`: properly appends child at the node that already has children" $
        (Path.with (Path [ 0 ]) (Tree.appendChild $ ql "d") $ "a" :< [ "b" :<~ [ "c" ] ])
        `compareTrees`
        ("a" :< [ "b":<~ [ "c", "d" ] ])

      it "`with`: properly appends child at some deeper node" $
        (Path.with (Path [ 2, 1 ]) (Tree.appendChild $ ql "h")
          $ "a" :< [ ql "b", ql "c", "d" :<~ [ "e", "f", "g" ], ql "x", ql "y" ])
        `compareTrees`
        ("a" :< [ ql "b", ql "c", "d" :< [ ql "e", "f" :<~ [ "h" ], ql "g" ], ql "x", ql "y" ])

      it "`with`: properly appends child at the deeper node that already has children" $
        (Path.with (Path [ 2, 1 ]) (Tree.appendChild $ ql "i")
          $ "a" :< [ ql "b", ql "c", "d" :< [ ql "e", "f" :<~ [ "h" ], ql "g" ], ql "x", ql "y" ])
        `compareTrees`
        ("a" :< [ ql "b", ql "c", "d" :< [ ql "e", "f" :<~ [ "h", "i" ], ql "g" ], ql "x", ql "y" ])

    describe "`traverse`" $ do

      let collectData path value node = { path, value, children : Array.length $ Tree.children node }

      it "`traverse` on a one-leaf tree" $
        (Path.traverse collectData $ ql "a")
        `compareTrees`
        (ql { path : Path [], value : "a", children : 0 })
      it "`traverse` on a node with children" $
        (Path.traverse collectData
          $ "a" :<~ [ "b", "c", "d", "e" ]
        )
        `compareTrees`
        ({ path : Path [], value : "a", children : 4 } :<~
          [ { path : Path [0], value : "b", children : 0 }
          , { path : Path [1], value : "c", children : 0 }
          , { path : Path [2], value : "d", children : 0 }
          , { path : Path [3], value : "e", children : 0 }
          ]
        )
      it "`traverse` on a node with children 2" $
        (Path.traverse collectData
          $ "a" :< [ ql "b", ql "c", "d" :< [], ql "e" ]
        )
        `compareTrees`
        ({ path : Path [], value : "a", children : 4 } :<
          [ ql { path : Path [0], value : "b", children : 0 }
          , ql { path : Path [1], value : "c", children : 0 }
          ,    { path : Path [2], value : "d", children : 0 } :< []
          , ql { path : Path [3], value : "e", children : 0 }
          ]
        )
      it "`traverse` on a node with deeper children" $
        (Path.traverse collectData
          $ "a" :< [ ql "b", ql "c", "d" :< [ ql "q", ql "r", ql "s" ], ql "e" ]
        )
        `compareTrees`
        ({ path : Path [], value : "a", children : 4 } :<
          [ ql { path : Path [0], value : "b", children : 0 }
          , ql { path : Path [1], value : "c", children : 0 }
          , { path : Path [2], value : "d", children : 3 } :<~
            [ { path : Path [2,0], value : "q", children : 0 }
            , { path : Path [2,1], value : "r", children : 0 }
            , { path : Path [2,2], value : "s", children : 0 }
            ]
          , ql { path : Path [3], value : "e", children : 0 }
          ]
        )

    describe "`find`" $ do

      let

        -- findIn :: forall (m :: Type -> Type) a. MonadThrow Ex.Error m => Show a => Tree a -> Path -> Tree a -> m Unit
        findIn tree path expected =
          case Path.find path tree of
            Just found ->
              found `compareTrees` expected
            Nothing -> fail $ treeToString expected <> " wasn't found at " <> show path

        -- failToFind :: forall (m :: Type -> Type) a. MonadThrow Ex.Error m => Show a => Tree a -> Path -> m Unit
        failToFind tree path =
          case Path.find path tree of
            Just what ->
              fail $ "expected to find nothing at " <> show path <> ", but found " <> treeToString what
            Nothing -> pure unit

      it "`find` on a one-leaf tree" $
        findIn (ql "a") (Path []) (ql "a")
      it "`find` on a node with children" $ do
        let tree = "a" :<~ [ "b", "c", "d", "e" ]
        findIn tree (Path []) ("a" :<~ [ "b", "c", "d", "e" ])
        findIn tree (Path [1]) (ql "c")
        findIn tree (Path [3]) (ql "e")
      it "`find` on a node with children 2" $ do
        let tree = "a" :< [ ql "b", ql "c", "d" :< [], ql "e" ]
        findIn tree (Path []) ("a" :< [ ql "b", ql "c", "d" :< [], ql "e" ])
        findIn tree (Path [1]) (ql "c")
        findIn tree (Path [2]) ("d" :< [])
        findIn tree (Path [3]) (ql "e")
      it "`find` on a node with deeper children" $ do
        let tree = "a" :< [ ql "b", ql "c", "d" :<~ [ "q", "r", "s" ], ql "e" ]
        findIn tree (Path []) ("a" :< [ ql "b", ql "c", "d" :<~ [ "q", "r", "s" ], ql "e" ])
        findIn tree (Path [1]) (ql "c")
        findIn tree (Path [2]) ("d" :<~ [ "q", "r", "s" ])
        findIn tree (Path [3]) (ql "e")
        findIn tree (Path [2, 1]) (ql "r")
        findIn tree (Path [2, 2]) (ql "s")
        failToFind tree (Path [1, 1])
        failToFind tree (Path [2, 7])

    describe "`edges`" $ do

      it "`edges` of the tree node" $ do
        let tree = "a" :< [ ql "b", ql "c", "d" :<~ [ "q", "r", "s" ], ql "e" ]
        Tree.edges tree `shouldEqual` [ "a" /\ "b", "a" /\ "c", "a" /\ "d", "a" /\ "e", "d" /\ "q", "d" /\ "r", "d" /\ "s" ]

    describe "path" $ do

      let tree = "a" :< [ ql "b", ql "c", "d" :<~ [ "q", "r", "s" ], ql "e" ]

      it "properly detects `startsWith`" $ do
        Path.startsWith (Path [ 1 ]) Path.root `shouldEqual` true
        Path.startsWith Path.root (Path [ 1 ]) `shouldEqual` false
        Path.startsWith (Path [ 1, 2, 3 ]) (Path [ 1 ]) `shouldEqual` true
        Path.startsWith (Path [ 3, 2, 1 ]) (Path [ 1 ]) `shouldEqual` false
        Path.startsWith (Path [ 2, 2, 2 ]) (Path [ 2 ]) `shouldEqual` true
        Path.startsWith (Path [ 2, 2, 2 ]) (Path [ 2, 2 ]) `shouldEqual` true

      it "properly detects `nextFor`" $ do
        Path.isNextFor (Path [ 1 ]) Path.root `shouldEqual` true
        Path.isNextFor (Path [ 1, 2 ]) Path.root `shouldEqual` false
        Path.isNextFor Path.root (Path [ 1 ]) `shouldEqual` false
        Path.isNextFor (Path [ 1, 2, 3 ]) (Path [ 1, 2 ]) `shouldEqual` true

      it "`safeAdvance`" $ do
        Path.safeAdvance (Path [ ]) 0 tree `shouldEqual` (Path [ 0 ]) -- first child exists, go to `b`
        Path.safeAdvance (Path [ ]) 3 tree `shouldEqual` (Path [ 3 ]) -- fourth (index 3) child exists, go to `e`
        Path.safeAdvance (Path [ ]) 4 tree `shouldEqual` (Path [ ])  -- no fifth child, stay at `a`
        Path.safeAdvance (Path [ ]) (-1) tree `shouldEqual` (Path [ ]) -- couldn't go in negative direction, stay at `a`
        Path.safeAdvance (Path [ 0 ]) 0 tree `shouldEqual` (Path [ 0 ]) -- first child exists
        Path.safeAdvance (Path [ 0, 0 ]) 0 tree `shouldEqual` (Path [ 0, 0 ]) -- no children deeper, stays at `b`
        Path.safeAdvance (Path [ 2 ]) 1 tree `shouldEqual` (Path [ 2, 1 ]) -- at `r`
        Path.safeAdvance (Path [ 2 ]) 3 tree `shouldEqual` (Path [ 2 ]) -- not enough children: [ "q", "r", "s" ]

      it "properly navigates in the tree: up" $ do
        Path.advanceDir Path.root Path.Up tree `shouldEqual` Path.root -- no way up above the root
        Path.advanceDir (Path [ 1 ]) Path.Up tree `shouldEqual` Path.root -- from one level deep to the root
        Path.advanceDir (Path [ 2, 1 ]) Path.Up tree `shouldEqual` (Path [ 2 ]) -- one level up

      it "properly navigates in the tree: down" $ do
        Path.advanceDir Path.root Path.Down tree `shouldEqual` (Path [ 0 ]) -- to the first child
        Path.advanceDir (Path [ 1 ]) Path.Down tree `shouldEqual` (Path [ 1 ]) -- nothing is deeper, stays at `c`
        Path.advanceDir (Path [ 2 ]) Path.Down tree `shouldEqual` (Path [ 2, 0 ]) -- one level down to `q`

      it "properly navigates in the tree: right" $ do
        Path.advanceDir (Path [ 2, 0 ]) Path.Right tree `shouldEqual` (Path [ 2, 1 ]) -- next child after `q` is `r`
        Path.advanceDir (Path [ 2, 2 ]) Path.Right tree `shouldEqual` (Path [ 2, 2 ]) -- no child next to `s`, stays the same
        Path.advanceDir (Path [ 1 ]) Path.Right tree `shouldEqual` (Path [ 2 ]) -- next to `c` is `d`
        Path.advanceDir Path.root Path.Right tree `shouldEqual`(Path.root) -- only root is next to the root

      it "properly navigates in the tree: left" $ do
        Path.advanceDir (Path [ 2, 0 ]) Path.Left tree `shouldEqual` (Path [ 2, 0 ]) -- already at `q`, the begiining, no way to the left
        Path.advanceDir (Path [ 2, 2 ]) Path.Left tree `shouldEqual` (Path [ 2, 1 ]) -- go from `s` to `r`
        Path.advanceDir (Path [ 1 ]) Path.Left tree `shouldEqual` (Path [ 0 ]) -- previous for `c` is `b`
        Path.advanceDir Path.root Path.Left tree `shouldEqual`(Path.root) -- only root is next to the root


    describe "rebuilding" $ do

      let
        srcTree = "a" :< [ ql "b", ql "c", "d" :<~ [ "q", "r", "s" ], ql "e" ]

      it "properly rebuilds tree by adding children with `rebuildTree`" $
        let
          rebuiltTree =
              srcTree
                  # Tree.alter
                    \symb cs ->
                        if symb == "c" then
                            "+" /\ [ ql "x", ql "y", ql "z" ]
                        else symb /\ cs
          expectedTree = "a" :< [ ql "b", "+" :<~ [ "x", "y", "z" ], "d" :<~ [ "q", "r", "s" ], ql "e" ]
        in rebuiltTree `compareTrees` expectedTree

      it "properly rebuilds tree by adding children with `rebuildTree` deeper" $
        let
          rebuiltTree =
              srcTree
                  # Tree.alter
                    \symb cs ->
                        if symb == "r" then
                            "r" /\ [ ql "rr", ql "rs", ql "rt" ]
                        else symb /\ cs
          expectedTree = "a" :< [ ql "b", ql "c", "d" :< [ ql "q", "r" :<~ [ "rr", "rs", "rt" ], ql "s" ], ql "e" ]
        in rebuiltTree `compareTrees` expectedTree

      it "removes chidren with `rebuildTree`" $
        let
          rebuiltTree =
              srcTree
                  # Tree.alter
                    \symb cs -> if symb == "d" then "d" /\ [] else symb /\ cs
          expectedTree = "a" :<~ [ "b", "c", "d", "e" ]
        in rebuiltTree `compareTrees` expectedTree

      it "move the structure deeper with `rebuildTree`" $
        let
          rebuiltTree =
              srcTree
                  # Tree.alter
                    \symb cs -> if symb == "d" then "foo" /\ [ "d" :< cs ] else symb /\ cs
          expectedTree = "a" :< [ ql "b", ql "c", "foo" :< [ "d" :<~ [ "q", "r", "s" ] ], ql "e" ]
        in rebuiltTree `compareTrees` expectedTree

      it "split the structure at some level with `rebuildTree`" $
        let
          breakF "q" cs = Tree.node "foo" [ "q" :< cs ]
          breakF "r" cs = Tree.node "bar" [ "r" :< cs ]
          breakF "t" cs = Tree.node "buz" [ "t" :< cs ]
          breakF   x cs = Tree.node    x  [   x :< cs ]
          rebuiltTree =
              srcTree
                  # Tree.alter
                    \symb cs ->
                      if symb == "d" then "d" /\ (Tree.break breakF <$> cs) else symb /\ cs
          expectedTree = "a" :< [ ql "b", ql "c", "d" :< [ "foo" :<~ [ "q" ], "bar" :<~ [ "r" ], "s" :<~ [ "s" ] ], ql "e" ]

        in rebuiltTree `compareTrees` expectedTree

    describe "regrouping" $ do

      let
        srcTree = 0 :<~ [ 10, 11, 12, 20, 22, 33, 35, 49, 77 ]

      it "properly rebuilds tree by adding children with `rebuildTree`" $
        let
          regroupedTree = srcTree # Tree.regroup (_ == 0) (_ `div` 10) (_ * 10)
          expectedTree = 0 :< [ 10 :<~ [ 10, 11, 12 ], 20 :<~ [ 20, 22 ], 30 :<~ [ 33, 35 ], 40 :<~ [ 49 ], 70 :<~ [ 77 ] ]
        in regroupedTree `compareTrees` expectedTree

    describe "conversions" $ do

      it "`toString`: Indent" $ do

        (Convert.toString Convert.Indent show $ 1 :<
            [ ql 11
            , 12 :<~ [ 121, 122, 123 ]
            , 13 :<~ [ 131 ]
            , 14 :< [ ql 141, 142 :<~ [ 1421 ] ]
            , 15 :<~ [ 151, 152 ]
            , ql 16
            ])
        `shouldEqual` """1
 11
 12
  121
  122
  123
 13
  131
 14
  141
  142
   1421
 15
  151
  152
 16"""

      it "`toString`: Lines" $ do

        (Convert.toString Convert.Lines show $ 1 :<
            [ ql 11
            , 12 :<~ [ 121, 122, 123 ]
            , 13 :<~ [ 131 ]
            , 14 :< [ ql 141, 142 :<~ [ 1421 ] ]
            , 15 :<~ [ 151, 152 ]
            , ql 16
            ])
        `shouldEqual` """1
|-11
|-12
|--121
|--122
|--123
|-13
|--131
|-14
|--141
|--142
|---1421
|-15
|--151
|--152
|-16"""


      it "`toString`: Corners" $ do

        (Convert.toString Convert.Corners show $ 1 :<
            [ ql 11
            , 12 :<~ [ 121, 122, 123 ]
            , 13 :<~ [ 131 ]
            , 14 :< [ ql 141, 142 :<~ [ 1421 ] ]
            , 15 :<~ [ 151, 152 ]
            , ql 16
            ])
        `shouldEqual` """1
├11
├12
├├121
├├122
├└123
├13
├└131
├14
├├141
├└142
├├└1421
├15
├├151
├└152
└16"""  -- FIXME: `├├└1421` is not beautiful at all


      it "`toString`: Triangles" $ do

        (Convert.toString Convert.Triangles show $ 1 :<
            [ ql 11
            , 12 :<~ [ 121, 122, 123 ]
            , 13 :<~ [ 131 ]
            , 14 :< [ ql 141, 142 :<~ [ 1421 ] ]
            , 15 :<~ [ 151, 152 ]
            , ql 16
            ])
        `shouldEqual` """1
◦11
◦12
▹◦121
▹◦122
▹◦123
◦13
▹◦131
◦14
▹◦141
▹◦142
▹▹◦1421
◦15
▹◦151
▹◦152
◦16"""


      it "`fromString`: just root" $ do

        (Convert.fromString Int.fromString """1""" `compareTrees` (Tree.leaf $ Just 1))

      it "`fromString`: one-level nesting" $ do
        (Convert.fromString Int.fromString """1
 11
 12
 13"""
        `compareTrees`
        (Just <$> 1 :<~ [ 11, 12, 13 ]))

      it "`fromString`: deeper nesting" $ do
        (Convert.fromString Int.fromString """1
 11
 12
  121
  122
  123"""
        `compareTrees`
        (Just <$> 1 :< [ ql 11, 12 :<~ [ 121, 122, 123 ] ]))

      it "`fromString`: deeper nesting 2" $ do
        (Convert.fromString Int.fromString """1
 11
 12
  121
  122
  123
 13"""
        `compareTrees`
        (Just <$> 1 :< [ ql 11, 12 :<~ [ 121, 122, 123 ], ql 13 ]))


      it "`fromString`: deeper nesting with next children" $ do
        (Convert.fromString Int.fromString """1
 11
 12
  121
  122
  123
 13
  131
 14
 15"""
        `compareTrees`
        (Just <$> 1 :< [ ql 11, 12 :<~ [ 121, 122, 123 ], 13 :<~ [ 131 ], ql 14, ql 15 ]))

      it "`fromString`: deeper nesting with next children 2" $ do
        (Convert.fromString Int.fromString """1
 11
 12
  121
  122
  123
 13
  131
 14
  141
  142
   1421
 15
  151
  152
 16"""
        `compareTrees`
        (Just <$>
          1 :<
            [ ql 11
            , 12 :<~ [ 121, 122, 123 ]
            , 13 :<~ [ 131 ]
            , 14 :< [ ql 141, 142 :<~ [ 1421 ] ]
            , 15 :<~ [ 151, 152 ]
            , ql 16
            ])
        )

      it "`fromJson` / `toJson`: test converts to JSON and back" $ do
        let
          testTree =
            1 :<
              [ ql 11
              , 12 :<~ [ 121, 122, 123 ]
              , 13 :<~ [ 131 ]
              , 14 :< [ ql 141, 142 :<~ [ 1421 ] ]
              , 15 :<~ [ 151, 152 ]
              , ql 16
              ]
          (convResult :: E (Tree Int)) = Convert.readJSON $ Convert.writeJSON testTree
        case convResult of
          Left errs -> fail $ String.joinWith ", " $ renderForeignError <$> Array.fromFoldable errs
          Right convertedTree ->
            testTree `compareTrees` convertedTree


      {-
      it "`toDot`" $ do
        let
          testTree =
            1 :<
              [ ql 11
              , 12 :<~ [ 121, 122, 123 ]
              , 13 :<~ [ 131 ]
              , 14 :< [ ql 141, 142 :<~ [ 1421 ] ]
              , 15 :<~ [ 151, 152, 11 ]
              , ql 16
              ]
        Convert.toDotText show testTree
        `shouldEqual`
        "digraph {1 []; 11 []; 12 []; 121 []; 122 []; 123 []; 13 []; 131 []; 14 []; 141 []; 142 []; 1421 []; 15 []; 151 []; 152 []; 11 []; 16 []; 1 -> 11; 1 -> 12; 1 -> 13; 1 -> 14; 1 -> 15; 1 -> 16; 12 -> 121; 12 -> 122; 12 -> 123; 13 -> 131; 14 -> 141; 14 -> 142; 142 -> 1421; 15 -> 151; 15 -> 152; 15 -> 11; }"

      it "`toDot` v.2" $ do
        let
          testTree =
            1 :<
              [ ql 11
              , 12 :<~ [ 121, 122, 123 ]
              , 13 :<~ [ 131 ]
              , 14 :< [ ql 141, 142 :<~ [ 1421 ] ]
              , 15 :<~ [ 151, 152, 11 ]
              , ql 16
              ]
          toDotId path v =
            -- just the path is enough for uniqueness
            Convert.DotId $ "\"" <> Path.dashed path <> "::" <> show v <> "\""
          toLabel path v =
            show v
        Convert.toDotText' (Convert.dotConvertWithLabel toDotId toLabel) testTree
        `shouldEqual`
        """digraph {"*::1" [label="1"]; "0::11" [label="11"]; "1::12" [label="12"]; "1-0::121" [label="121"]; "1-1::122" [label="122"]; "1-2::123" [label="123"]; "2::13" [label="13"]; "2-0::131" [label="131"]; "3::14" [label="14"]; "3-0::141" [label="141"]; "3-1::142" [label="142"]; "3-1-0::1421" [label="1421"]; "4::15" [label="15"]; "4-0::151" [label="151"]; "4-1::152" [label="152"]; "4-2::11" [label="11"]; "5::16" [label="16"]; "*::1" -> "0::11"; "*::1" -> "1::12"; "*::1" -> "2::13"; "*::1" -> "3::14"; "*::1" -> "4::15"; "*::1" -> "5::16"; "1::12" -> "1-0::121"; "1::12" -> "1-1::122"; "1::12" -> "1-2::123"; "2::13" -> "2-0::131"; "3::14" -> "3-0::141"; "3::14" -> "3-1::142"; "3-1::142" -> "3-1-0::1421"; "4::15" -> "4-0::151"; "4::15" -> "4-1::152"; "4::15" -> "4-2::11"; }"""
      -}


treeToString :: forall a. Show a => Tree a -> String
treeToString = Convert.toString Convert.Dashes show


compareTrees ∷ forall (m :: Type -> Type) (a ∷ Type) (b ∷ Type). MonadThrow Ex.Error m => Show a => Show b => Tree a -> Tree b -> m Unit
compareTrees treeA treeB =
  (treeToString treeA) `shouldEqual` (treeToString treeB)