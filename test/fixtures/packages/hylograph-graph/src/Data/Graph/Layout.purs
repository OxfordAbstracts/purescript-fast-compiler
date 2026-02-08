-- | Layout algorithms for graph and tree visualization
-- |
-- | Provides pure layout algorithms that compute node positions.
-- | Works with any node identifier type.
module Data.Graph.Layout
  ( -- * Types
    TreeLayout(..)
  , Point
  , LayoutNode
  , LayoutConfig
    -- * Tree Layouts
  , treeLayout
  , layeredTreeLayout
  , defaultLayoutConfig
    -- * DAG Layouts (Sugiyama-style)
  , dagLayout
  , sugiyamaLayout
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl, maximum)
import Data.Int as Int
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple (Tuple(..))

-- =============================================================================
-- Types
-- =============================================================================

-- | Tree layout orientation
data TreeLayout = Radial | Horizontal | Vertical

derive instance eqTreeLayout :: Eq TreeLayout
derive instance ordTreeLayout :: Ord TreeLayout

instance showTreeLayout :: Show TreeLayout where
  show Radial = "Radial"
  show Horizontal = "Horizontal"
  show Vertical = "Vertical"

-- | A 2D point
type Point = { x :: Number, y :: Number }

-- | A node with computed layout position
type LayoutNode node =
  { id :: node
  , x :: Number
  , y :: Number
  , layer :: Int  -- Depth/layer in hierarchical layout
  }

-- | Configuration for layout algorithms
type LayoutConfig =
  { nodeWidth :: Number      -- Spacing between nodes within a layer
  , nodeHeight :: Number     -- Spacing between layers
  , orientation :: TreeLayout
  , reversed :: Boolean      -- Reverse layer direction (right-to-left for Horizontal, bottom-to-top for Vertical)
  }

-- | Default layout configuration
defaultLayoutConfig :: LayoutConfig
defaultLayoutConfig =
  { nodeWidth: 100.0
  , nodeHeight: 80.0
  , orientation: Vertical
  , reversed: false
  }

-- =============================================================================
-- Tree Layout (for rooted trees)
-- =============================================================================

-- | Adjacency representation for trees
type TreeAdj node = Map node (Array node)

-- | Compute tree layout with the given root node
-- |
-- | Uses a simple recursive algorithm:
-- | - Children are placed side by side
-- | - Parent is centered above its children
treeLayout :: forall node. Ord node => LayoutConfig -> node -> TreeAdj node -> Array (LayoutNode node)
treeLayout config root adj =
  let
    -- Compute subtree widths for centering
    widths = computeWidths root adj

    -- Compute positions starting from root at (0, 0)
    positions = computePositions config widths 0 0.0 root adj
  in
    Map.toUnfoldable positions <#> \(Tuple id pos) ->
      { id, x: pos.x, y: pos.y, layer: pos.layer }

-- | Compute the width of each subtree (number of leaf descendants)
computeWidths :: forall node. Ord node => node -> TreeAdj node -> Map node Int
computeWidths root adj = snd $ go root
  where
  go :: node -> Tuple Int (Map node Int)
  go node =
    case Map.lookup node adj of
      Nothing -> Tuple 1 (Map.singleton node 1)
      Just [] -> Tuple 1 (Map.singleton node 1)
      Just children ->
        let childResults = children <#> go
            childWidths = childResults <#> fst
            totalWidth = max 1 (foldl (+) 0 childWidths)
            childMaps = childResults <#> snd
            mergedMaps = foldl Map.union Map.empty childMaps
        in Tuple totalWidth (Map.insert node totalWidth mergedMaps)

-- | Compute positions for all nodes
computePositions :: forall node. Ord node
  => LayoutConfig
  -> Map node Int  -- Subtree widths
  -> Int           -- Current depth
  -> Number        -- Current left offset
  -> node          -- Current node
  -> TreeAdj node
  -> Map node { x :: Number, y :: Number, layer :: Int }
computePositions config widths depth leftOffset node adj =
  let
    nodeWidth = fromMaybe 1 $ Map.lookup node widths
    myX = leftOffset + toNumber nodeWidth * config.nodeWidth / 2.0
    myY = toNumber depth * config.nodeHeight

    myPos = case config.orientation of
      Horizontal -> { x: myY, y: myX, layer: depth }
      Vertical -> { x: myX, y: myY, layer: depth }
      Radial -> { x: myX, y: myY, layer: depth }  -- Radial needs post-processing

    children = fromMaybe [] $ Map.lookup node adj

    -- Compute child positions
    result = foldl (\{ offset, positions } child ->
      let childWidth = fromMaybe 1 $ Map.lookup child widths
          childPositions = computePositions config widths (depth + 1) offset child adj
      in { offset: offset + toNumber childWidth * config.nodeWidth
         , positions: Map.union positions childPositions
         }
    ) { offset: leftOffset, positions: Map.empty } children
  in
    Map.insert node myPos result.positions

-- =============================================================================
-- Layered Tree Layout (for already-layered nodes)
-- =============================================================================

-- | Node with layer information
type LayeredInput node =
  { id :: node
  , layer :: Int
  , children :: Array node
  }

-- | Layout nodes that already have layer assignments
-- |
-- | Useful when you've computed layers separately (e.g., from topological sort).
layeredTreeLayout :: forall node. Ord node
  => LayoutConfig
  -> Array (LayeredInput node)
  -> Array (LayoutNode node)
layeredTreeLayout config nodes =
  let
    -- Group nodes by layer
    layerGroups = foldl (\acc n ->
      Map.alter (Just <<< Array.cons n.id <<< fromMaybe []) n.layer acc
    ) Map.empty nodes

    -- Compute x positions within each layer
    positions = (Map.toUnfoldable layerGroups :: Array (Tuple Int (Array node))) # foldl (\acc (Tuple layer nodeIds) ->
      let
        count = Array.length nodeIds
        startX = -(toNumber (count - 1) * config.nodeWidth / 2.0)
      in foldl (\a (Tuple idx nodeId) ->
           let x = startX + toNumber idx * config.nodeWidth
               y = toNumber layer * config.nodeHeight
           in Map.insert nodeId { x, y, layer } a
         ) acc (Array.mapWithIndex (\i n -> Tuple i n) nodeIds)
    ) Map.empty
  in
    nodes <#> \n ->
      case Map.lookup n.id positions of
        Nothing -> { id: n.id, x: 0.0, y: 0.0, layer: n.layer }
        Just pos -> { id: n.id, x: pos.x, y: pos.y, layer: pos.layer }

-- =============================================================================
-- DAG Layout (Sugiyama-style)
-- =============================================================================

-- | Simple graph adjacency for layout
type GraphAdj node = Map node (Set node)

-- | Layout a DAG using Sugiyama-style algorithm
-- |
-- | Steps:
-- | 1. Compute layers (topological)
-- | 2. Order nodes within layers to minimize crossings
-- | 3. Assign x coordinates
dagLayout :: forall node. Ord node
  => LayoutConfig
  -> Array node          -- All nodes (in any order)
  -> GraphAdj node       -- Edges (node -> targets)
  -> Array (LayoutNode node)
dagLayout = sugiyamaLayout

-- | Sugiyama hierarchical layout algorithm
-- |
-- | A simplified version that:
-- | 1. Assigns layers based on longest path from sources
-- | 2. Orders nodes to reduce crossings (barycenter heuristic)
-- | 3. Assigns coordinates
sugiyamaLayout :: forall node. Ord node
  => LayoutConfig
  -> Array node
  -> GraphAdj node
  -> Array (LayoutNode node)
sugiyamaLayout config nodes edges =
  let
    -- Step 1: Assign layers (longest path from sources)
    layers = assignLayers nodes edges

    -- Step 2: Group by layer and order within layers
    layerGroups = groupByLayer nodes layers

    -- Step 3: Order nodes within layers (barycenter method)
    orderedLayers = orderLayers layerGroups edges

    -- Step 4: Assign coordinates
    positions = assignCoordinates config orderedLayers
  in
    nodes # Array.mapMaybe \node ->
      case Map.lookup node positions of
        Nothing -> Nothing
        Just pos -> Just { id: node, x: pos.x, y: pos.y, layer: pos.layer }

-- | Assign layers based on longest path from source nodes
assignLayers :: forall node. Ord node => Array node -> GraphAdj node -> Map node Int
assignLayers nodes edges =
  let
    -- Find nodes with no incoming edges (sources)
    allTargets = foldl (\acc targets -> Set.union acc targets)
                   Set.empty (Map.values edges)
    sources = Array.filter (\n -> not (Set.member n allTargets)) nodes

    -- BFS from sources, tracking max depth
    go :: Array node -> Int -> Map node Int -> Map node Int
    go [] _ layers = layers
    go frontier depth layers =
      let
        -- Update layers for frontier nodes
        layers' = foldl (\acc n ->
          let currentLayer = fromMaybe 0 $ Map.lookup n acc
          in Map.insert n (max currentLayer depth) acc
        ) layers frontier

        -- Find next frontier (children of current frontier)
        nextFrontier = Array.nub $ Array.concatMap (\n ->
          case Map.lookup n edges of
            Nothing -> []
            Just targets -> Set.toUnfoldable targets
        ) frontier
      in go nextFrontier (depth + 1) layers'

    -- Initialize with sources at layer 0
    initialLayers = Map.fromFoldable $ sources <#> \n -> Tuple n 0
  in
    go sources 0 initialLayers

-- | Group nodes by their assigned layer
groupByLayer :: forall node. Ord node
  => Array node
  -> Map node Int
  -> Map Int (Array node)
groupByLayer nodes layers =
  foldl (\acc node ->
    let layer = fromMaybe 0 $ Map.lookup node layers
    in Map.alter (Just <<< Array.cons node <<< fromMaybe []) layer acc
  ) Map.empty nodes

-- | Order nodes within layers using barycenter heuristic
-- |
-- | Nodes are ordered by the average position of their neighbors
-- | in the previous layer.
orderLayers :: forall node. Ord node
  => Map Int (Array node)
  -> GraphAdj node
  -> Map Int (Array node)
orderLayers layerGroups edges =
  let
    numLayers = fromMaybe 0 $ maximum $ Map.keys layerGroups

    -- Build reverse edges for looking up parents
    reverseEdges = buildReverseEdges' edges

    -- Iterate through layers, ordering based on previous layer
    go :: Int -> Map Int (Array node) -> Map Int (Array node)
    go layer groups
      | layer > numLayers = groups
      | otherwise =
          let
            prevLayerNodes = fromMaybe [] $ Map.lookup (layer - 1) groups
            prevPositions = Map.fromFoldable $
              Array.mapWithIndex (\i n -> Tuple n (toNumber i)) prevLayerNodes

            currentNodes = fromMaybe [] $ Map.lookup layer groups

            -- Compute barycenter for each node
            barycenters = currentNodes <#> \node ->
              let parents = fromMaybe Set.empty $ Map.lookup node reverseEdges
                  parentPositions = Array.mapMaybe (\p -> Map.lookup p prevPositions)
                                      (Set.toUnfoldable parents)
                  avg = if Array.length parentPositions == 0
                        then 0.0
                        else foldl (+) 0.0 parentPositions / toNumber (Array.length parentPositions)
              in Tuple avg node

            -- Sort by barycenter
            sorted = Array.sortWith fst barycenters <#> snd

            groups' = Map.insert layer sorted groups
          in go (layer + 1) groups'
  in
    go 1 layerGroups

-- | Build reverse edges (target -> sources)
buildReverseEdges' :: forall node. Ord node => GraphAdj node -> Map node (Set node)
buildReverseEdges' edges =
  foldl (\acc (Tuple source targets) ->
    foldl (\a target ->
      Map.alter (Just <<< Set.insert source <<< fromMaybe Set.empty) target a
    ) acc (Set.toUnfoldable targets :: Array node)
  ) Map.empty (Map.toUnfoldable edges :: Array (Tuple node (Set node)))

-- | Assign x,y coordinates based on layer ordering
-- | Respects orientation: Vertical (layers top-to-bottom), Horizontal (layers left-to-right)
-- | When reversed: Vertical = bottom-to-top, Horizontal = right-to-left
assignCoordinates :: forall node. Ord node
  => LayoutConfig
  -> Map Int (Array node)
  -> Map node { x :: Number, y :: Number, layer :: Int }
assignCoordinates config layerGroups =
  let
    maxLayer = fromMaybe 0 $ maximum $ Map.keys layerGroups
  in
  foldl (\acc (Tuple layer nodes) ->
    let
      count = Array.length nodes
      -- Position along the layer (perpendicular to layer direction)
      startCross = -(toNumber (count - 1) * config.nodeWidth / 2.0)
      -- Position of the layer itself (optionally reversed)
      effectiveLayer = if config.reversed then maxLayer - layer else layer
      layerPos = toNumber effectiveLayer * config.nodeHeight
    in foldl (\a (Tuple idx node) ->
         let crossPos = startCross + toNumber idx * config.nodeWidth
             -- Apply orientation: Vertical = layers are rows, Horizontal = layers are columns
             pos = case config.orientation of
               Vertical -> { x: crossPos, y: layerPos, layer }
               Horizontal -> { x: layerPos, y: crossPos, layer }
               Radial -> { x: crossPos, y: layerPos, layer }  -- Radial needs post-processing
         in Map.insert node pos a
       ) acc (Array.mapWithIndex (\i n -> Tuple i n) nodes)
  ) Map.empty (Map.toUnfoldable layerGroups :: Array (Tuple Int (Array node)))

-- =============================================================================
-- Helpers
-- =============================================================================

toNumber :: Int -> Number
toNumber = Int.toNumber

fst :: forall a b. Tuple a b -> a
fst (Tuple a _) = a

snd :: forall a b. Tuple a b -> b
snd (Tuple _ b) = b
