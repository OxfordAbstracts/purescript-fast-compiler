module VISX.Layout.Hierarchy where

import Prelude
import Data.Function.Uncurried (Fn2)
import Prim.Row (class Lacks, class Union)
import React.Basic (JSX, ReactComponent)
import Record (insert)
import Type.Prelude (Proxy(..))

childrenProxy ∷ Proxy "children"
childrenProxy = Proxy

newtype Hierarchical v
  = Hierarchical { children ∷ Array (Hierarchical v) | v }

mkNode ∷ ∀ v. Lacks "children" v ⇒ { | v } → Array (Hierarchical v) → (Hierarchical v)
mkNode v children = Hierarchical $ insert childrenProxy children v

mkLeaf ∷ ∀ v. Lacks "children" v ⇒ { | v } → Hierarchical v
mkLeaf = Hierarchical <<< insert childrenProxy []

foreign import data Hierarchy ∷ Row Type → Type

foreign import hierarchy ∷ ∀ a. Hierarchical a → Hierarchy a

type HierarchyPointNode a
  = { | a }
type HierarchyCircularNode a
  = { | a }

type ClusterProps a
  = ( root ∷ Hierarchy a
    , children ∷ HierarchyPointNode a → JSX
    , className ∷ String
    , left ∷ Number
    , linkComponent ∷ ∀ r. ReactComponent r
    , nodeComponent ∷ ∀ r. ReactComponent r
    , nodeSize ∷ Array Number -- [width, height]
    , separation ∷ Fn2 (HierarchyPointNode a) (HierarchyPointNode a) Number
    , size ∷ Array Number -- [width, height]
    , top ∷ Number
    )
cluster ∷
  ∀ a attrs attrs_.
  Union attrs attrs_ (ClusterProps a) ⇒
  ReactComponent { root ∷ Hierarchy a | attrs }
cluster = clusterImpl
foreign import clusterImpl ∷ ∀ a. ReactComponent a

foreign import packImpl ∷ ∀ a. ReactComponent a
foreign import partitionImpl ∷ ∀ a. ReactComponent a
foreign import treeImpl ∷ ∀ a. ReactComponent a
foreign import treemapImpl ∷ ∀ a. ReactComponent a
