module Yoga.Tree.Extended where

import Prelude

import Control.Comonad.Cofree (head, tail, mkCofree, buildCofree) as Y
import Control.Comonad.Cofree

import Data.Maybe (Maybe(..), fromMaybe)
import Data.Array ((:))
import Data.Array (head, catMaybes, concat, drop, reverse, groupAllBy) as Array
import Data.Array.NonEmpty (head, toArray) as NEA
import Data.Tuple (uncurry) as Tuple
import Data.Tuple.Nested ((/\), type (/\))
import Data.Traversable (sequence)

import Yoga.Tree (Tree, leaf, mkTree, setNodeValue, modifyNodeValue) as Y


type Tree n = Y.Tree n


{-| Create tree from given single value. |-}
leaf :: forall n. n -> Tree n
leaf = Y.leaf


{-| Create tree from given value and its children. |-}
node :: forall n. n -> Array (Tree n) -> Tree n
node = Y.mkTree


{-| Get value of this tree node. |-}
value :: forall n. Tree n -> n
value = Y.head


{-| Get children of the this tree node. |-}
children :: forall n. Tree n -> Array (Tree n)
children = Y.tail


{-| Build tree starting from seed and getting further with every step using the next seeds provided in response. |-}
build :: forall s n. (s -> n /\ Array s) -> s -> Tree n
build = Y.buildCofree


{-| Traverse the nodes of given tree with the function, building a new tree with updated values and children.
Notice that children are incoming being aready modified by the same function, so if you return empty array for chidren, nothing
will come in later and the try won't visit deeper values. And vice versa. |-}
alter :: forall a b. (a -> Array (Tree b) -> b /\ Array (Tree b)) -> Tree a -> Tree b
alter f = break \a as -> Tuple.uncurry node $ f a $ alter f <$> as


{-| Traverse the nodes of given tree with the function, building a new tree with updated values and children |-}
alter' :: forall a b. (a -> b /\ Array (Tree b)) -> Tree a -> Tree b
alter' f = alter $ const <<< f


infixr 5 lnodeOp as :<~


{-| Node that only has leaves |-}
lnodeOp :: forall n. n -> Array n -> Tree n
lnodeOp n ls = Y.mkCofree n $ leaf <$> ls


{-| Convert tree to a flat array structure:

```
Tree.flatten
    $ Tree.node 'a'
    $ [ Tree.leaf 'x'
        , Tree.leaf 'c'
        , Tree.node 'd'
            [ Tree.leaf '1', Tree.leaf '2', Tree.leaf '3' ]
        , Tree.leaf 'e'
    ]
```

becomes:

```
[ 'a', 'x', 'c', 'd', '1', '2', '3', 'e' ]
```
|-}
flatten :: forall a. Tree a -> Array a
flatten = break $ \v xs -> v : Array.concat (flatten <$> xs)


{-| Call this function on both the value and chidlren of this tree node. |-}
break :: forall n a. (n -> Array (Tree n) -> a) -> Tree n -> a
break f t =
    f (Y.head t) $ Y.tail t


{-| Set value of the tree node. |-}
set :: forall n. n -> Tree n -> Tree n
set = Y.setNodeValue


{-| Update value of the tree node using its current value. |-}
update :: forall n. (n -> n) -> Tree n -> Tree n
update = Y.modifyNodeValue


{-| Leave only `Just` values in the tree. |-}
catMaybes :: forall n. n -> Tree (Maybe n) -> Tree n
catMaybes rootDefault =
    break deleteMaybes
    where

        deleteMaybes :: Maybe n -> Array (Tree (Maybe n)) -> Tree n
        deleteMaybes mbVal =
            node (fromMaybe rootDefault mbVal) <<< Array.catMaybes <<< map sequence


{-| If the value in the node matches the first function, keep the value intact, but iterate
 over all the children of this node, group the array of children by key received using `a -> key` (`Array.groupAllBy`)
 function, and after that wrap the direct children back in the values using `key -> a` function, so that:

 `(0 :<~ [ 10, 11, 12, 20, 22, 33, 35, 49, 77 ])`
 after `regroup (_ == 0) (_ `div` 10) (_ * 10)`
 would become: `(0 :< [ 10 :<~ [ 10, 11, 12 ], 20 :<~ [ 20, 22 ], 30 :<~ [ 33, 35 ], 40 :<~ [ 49 ], 70 :<~ [ 77 ] ])`

 Notice that we need the exact root node(s) to restructure its/their children.
|-}
regroup :: forall a k. Ord k => (a -> Boolean) -> (a -> k) -> (k -> a) -> Tree a -> Tree a
regroup needsRegroup valToKey keyToVal =
    alter \v xs ->
      if needsRegroup v then
        v /\
        (xs
           # Array.groupAllBy compareF
           # map makeNodeF)
      else v /\ xs
    where
      compareF treeA treeB =
        compare (valToKey $ value treeA) (valToKey $ value treeB)
      makeNodeF nea =
        node (keyToVal $ valToKey $ value $ NEA.head nea)
          $ NEA.toArray nea


{-|

    Return a list of pairs `( x /\ y )`` where

        - `x` and `y`` are of type `n`
        - `(x /\ y)` is in the list if and only if `y` is a chiild of `x`.

-}
edges :: forall n. Tree n -> Array ( n /\ n )
edges tree =
    edgesAux { trees : [ tree ], edges : [] } #  _.edges # Array.reverse


type EdgeState n =
    { trees :: Array (Tree n), edges :: Array ( n /\ n ) }


edgesAux :: forall n. EdgeState n -> EdgeState n
edgesAux state =
    case Array.head state.trees of
        Nothing ->
            state

        Just tree ->
            let
                theChildren = children tree

                tos =
                    value <$> theChildren

                from =
                    value tree

                newEdges =
                    ( (\to -> from /\ to ) <$> tos) # Array.reverse
            in
            edgesAux
                { trees : theChildren <> Array.drop 1 state.trees
                , edges : newEdges <> state.edges
                }
