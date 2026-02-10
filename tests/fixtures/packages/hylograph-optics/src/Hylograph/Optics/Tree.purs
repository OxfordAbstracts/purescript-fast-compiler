-- | Tree Optics
-- |
-- | Lenses, traversals, and folds for rose trees.
-- | These optics work with the Cofree-based Tree from psd3-tree.
module Hylograph.Optics.Tree
  ( -- * Basic Lenses
    _root
  , _children
  , _forest
    -- * Traversals
  , _leaves
  , _branches
  , _atDepth
  , _allNodes
    -- * Indexed Access
  , _childAt
  , nodeAtPath
    -- * Predicates
  , _matching
  ) where

import Prelude

import Control.Comonad.Cofree (Cofree, head, tail, mkCofree)
import Data.Lens (Lens', Traversal', lens, traversed, wander)
import Data.Lens.Fold (filtered)
import Data.List (List(..), (!!), updateAt, length)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Traversable (class Traversable, traverse)
import Data.Tree (Tree, Forest)

-- =============================================================================
-- Basic Lenses
-- =============================================================================

-- | Focus on the root value of a tree.
-- |
-- | ```purescript
-- | view _root (mkTree 1 [mkTree 2 [], mkTree 3 []])
-- | -- => 1
-- |
-- | set _root 100 tree
-- | -- Changes root to 100, children unchanged
-- | ```
_root :: forall a. Lens' (Tree a) a
_root = lens head \tree newRoot -> mkCofree newRoot (tail tree)

-- | Focus on the children of a tree (as a List of Trees).
-- |
-- | ```purescript
-- | view _children tree
-- | -- => List of child trees
-- |
-- | over _children (filter hasValue) tree
-- | -- Filter children by some predicate
-- | ```
_children :: forall a. Lens' (Tree a) (List (Tree a))
_children = lens tail \tree newChildren -> mkCofree (head tree) newChildren

-- | Alias for _children (Forest = List Tree)
_forest :: forall a. Lens' (Tree a) (Forest a)
_forest = _children

-- =============================================================================
-- Traversals
-- =============================================================================

-- | Traverse all leaf nodes (nodes with no children).
-- |
-- | ```purescript
-- | toListOf _leaves tree
-- | -- => List of all leaf values
-- |
-- | over _leaves (*2) tree
-- | -- Double all leaf values
-- | ```
_leaves :: forall a. Traversal' (Tree a) a
_leaves = _allNodes <<< filtered isLeaf <<< _root
  where
  isLeaf tree = length (tail tree) == 0

-- | Traverse all branch nodes (nodes with children).
-- |
-- | ```purescript
-- | toListOf _branches tree
-- | -- => List of all branch values
-- | ```
_branches :: forall a. Traversal' (Tree a) a
_branches = _allNodes <<< filtered isBranch <<< _root
  where
  isBranch tree = length (tail tree) > 0

-- | Traverse all nodes at a specific depth.
-- | Depth 0 is the root, depth 1 is immediate children, etc.
-- |
-- | ```purescript
-- | toListOf (_atDepth 2) tree
-- | -- => List of all grandchild values
-- | ```
_atDepth :: forall a. Int -> Traversal' (Tree a) a
_atDepth 0 = _root
_atDepth n = _children <<< traversed <<< _atDepth (n - 1)

-- | Traverse ALL nodes in the tree (pre-order).
-- | Note: This traverses subtrees, not just values.
-- |
-- | ```purescript
-- | toListOf _allNodes tree
-- | -- => Every subtree in the tree
-- | ```
_allNodes :: forall a. Traversal' (Tree a) (Tree a)
_allNodes = wander go
  where
  go :: forall f. Applicative f => (Tree a -> f (Tree a)) -> Tree a -> f (Tree a)
  go f tree =
    (\newTree newChildren -> mkCofree (head newTree) newChildren)
      <$> f tree
      <*> traverse (go f) (tail tree)

-- =============================================================================
-- Indexed Access
-- =============================================================================

-- | Focus on a specific child by index.
-- | Returns Nothing if index out of bounds.
-- |
-- | ```purescript
-- | preview (_childAt 0) tree
-- | -- => Maybe the first child
-- | ```
_childAt :: forall a. Int -> Lens' (Tree a) (Maybe (Tree a))
_childAt idx = lens getter setter
  where
  getter tree = tail tree !! idx
  setter tree mChild = mkCofree (head tree) $
    case mChild of
      Nothing -> tail tree
      Just child -> fromMaybe (tail tree) $ updateAt idx child (tail tree)

-- | Get the node at a path if it exists.
-- | This is a simple accessor, not an optic.
-- |
-- | ```purescript
-- | nodeAtPath [0, 1, 2] tree
-- | -- => Maybe the node at that path
-- | ```
nodeAtPath :: forall a. List Int -> Tree a -> Maybe (Tree a)
nodeAtPath Nil tree = Just tree
nodeAtPath (Cons idx rest) tree =
  case tail tree !! idx of
    Nothing -> Nothing
    Just child -> nodeAtPath rest child

-- =============================================================================
-- Predicate-based
-- =============================================================================

-- | Traverse nodes matching a predicate on their value.
-- |
-- | ```purescript
-- | toListOf (_matching (> 5)) tree
-- | -- => All node values greater than 5
-- |
-- | over (_matching isEven) (*2) tree
-- | -- Double all even values
-- | ```
_matching :: forall a. (a -> Boolean) -> Traversal' (Tree a) a
_matching pred = _allNodes <<< filtered (pred <<< head) <<< _root
