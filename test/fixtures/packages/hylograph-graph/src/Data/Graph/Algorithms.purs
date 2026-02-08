-- | Graph algorithms for directed graphs.
-- |
-- | This module provides a comprehensive suite of algorithms for analyzing
-- | directed graphs, including:
-- |
-- | - **Reachability**: BFS-based traversal to find all reachable nodes
-- | - **Topological Sort**: Layer computation for DAGs using `Data.Graph`
-- | - **Transitive Reduction**: Remove redundant edges while preserving reachability
-- | - **Cycle Detection**: DFS with three-color marking to find cycles
-- | - **Connected Components**: Find components treating graph as undirected
-- | - **Strongly Connected Components**: Tarjan's algorithm for directed components
-- | - **Centrality Measures**: In-degree, out-degree, and combined centrality
-- | - **PageRank**: Iterative importance scoring with configurable damping
-- | - **Community Detection**: Label propagation with modularity scoring
-- |
-- | All algorithms work with `SimpleGraph`, a simple adjacency-list representation.
-- | Convert to/from `TaskNode` arrays using the conversion utilities.
module Data.Graph.Algorithms
  ( -- Types
    SimpleGraph
  , TaskNode
  , LayeredNode
  , GraphMetrics
    -- Reachability
  , reachableFrom
    -- Topological sort
  , buildGraph
  , getTopologicalOrder
  , computeLayers
  , addLayers
    -- Transitive reduction
  , transitiveReduction
  , getRemovedEdges
  , getAllEdges
    -- Cycle detection
  , hasCycle
  , findCycle
  , isDAG
    -- Connected components
  , connectedComponents
  , isConnected
    -- Centrality
  , degreeCentrality
  , inDegreeCentrality
  , outDegreeCentrality
    -- Graph metrics
  , graphMetrics
  , density
  , averageDegree
    -- Strongly connected components
  , stronglyConnectedComponents
  , isSCC
    -- PageRank
  , pageRank
  , pageRankWithConfig
  , PageRankConfig
    -- Community detection
  , labelPropagation
  , modularity
    -- Conversion
  , taskNodesToSimpleGraph
  , simpleGraphToTaskNodes
  ) where

import Prelude

import Data.Array (concat, foldl, (\\))
import Data.Array as Array
import Data.Foldable (maximum)
import Data.Int as Int
import Data.Number (abs) as Number
import Data.Graph (Graph, fromMap, topologicalSort)
import Data.List (List)
import Data.List as List
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple (Tuple(..))

-- =============================================================================
-- || Simple Graph Representation (Adjacency List)
-- =============================================================================

-- | Simple graph as adjacency list (node -> set of targets)
type SimpleGraph node =
  { nodes :: Array node
  , edges :: Map node (Set node)
  }

-- =============================================================================
-- || Reachability Analysis
-- =============================================================================

-- | Compute all nodes reachable from a given node via BFS
-- | Uses tail recursion for efficiency
reachableFrom :: forall node. Ord node => node -> SimpleGraph node -> Set node
reachableFrom start graph =
  go Set.empty (Set.singleton start)
  where
    go :: Set node -> Set node -> Set node
    go visited frontier
      | Set.isEmpty frontier = visited
      | otherwise =
          let
            -- Get immediate neighbors of all frontier nodes
            neighbors = Set.unions $ Array.catMaybes $
              Set.toUnfoldable frontier <#> \n ->
                Map.lookup n graph.edges

            -- Only visit new nodes
            newNodes = Set.difference neighbors visited
          in
            go (Set.union visited frontier) newNodes

-- =============================================================================
-- || Topological Sort with Layers
-- =============================================================================

-- | A node with dependencies
type TaskNode node =
  { id :: node
  , depends :: Array node
  }

-- | A node with computed layer information
type LayeredNode node =
  { id :: node
  , layer :: Int
  , depends :: Array node
  }

-- | Build a Data.Graph from task nodes
-- | Graph k v = Graph (Map k (Tuple v (List k)))
buildGraph :: forall node. Ord node => Array (TaskNode node) -> Graph node (TaskNode node)
buildGraph tasks =
  let
    graphMap :: Map node (Tuple (TaskNode node) (List node))
    graphMap = foldl addTask Map.empty tasks

    addTask :: Map node (Tuple (TaskNode node) (List node)) -> TaskNode node -> Map node (Tuple (TaskNode node) (List node))
    addTask acc task =
      Map.insert task.id (Tuple task (List.fromFoldable task.depends)) acc
  in
    fromMap graphMap

-- | Get topological order using Data.Graph.topologicalSort
getTopologicalOrder :: forall node. Ord node => Array (TaskNode node) -> List node
getTopologicalOrder tasks =
  let graph = buildGraph tasks
  in topologicalSort graph

-- | Compute layers from topological sort
-- | Layer 0: nodes with no dependencies
-- | Layer N: nodes whose dependencies are all in layers < N
computeLayers :: forall node. Ord node => Array (TaskNode node) -> Map node Int
computeLayers tasks =
  let
    -- Reverse to get dependencies first
    sortedIds = List.reverse $ getTopologicalOrder tasks
    taskMap = Map.fromFoldable $ tasks <#> \t -> Tuple t.id t

    processTask :: Map node Int -> node -> Map node Int
    processTask accLayers taskId =
      case Map.lookup taskId taskMap of
        Nothing -> accLayers
        Just task ->
          let
            layer =
              if Array.null task.depends
                then 0
                else
                  -- All dependencies were processed earlier (topological order!)
                  let depLayers = task.depends <#> \depId ->
                        fromMaybe 0 $ Map.lookup depId accLayers
                  in case maximum depLayers of
                       Just maxLayer -> maxLayer + 1
                       Nothing -> 0
          in Map.insert taskId layer accLayers
  in
    foldl processTask Map.empty (List.toUnfoldable sortedIds :: Array node)

-- | Add layer information to task nodes
addLayers :: forall node. Ord node => Array (TaskNode node) -> Array (LayeredNode node)
addLayers tasks =
  let layers = computeLayers tasks
  in tasks <#> \t ->
       { id: t.id
       , layer: fromMaybe 0 $ Map.lookup t.id layers
       , depends: t.depends
       }

-- =============================================================================
-- || Transitive Reduction
-- =============================================================================

-- | Remove transitive edges from a graph
-- | An edge A → C is transitive if there exists a path A → B → C
-- | Returns a new graph with only the essential (non-transitive) edges
transitiveReduction :: forall node. Ord node => SimpleGraph node -> SimpleGraph node
transitiveReduction graph =
  { nodes: graph.nodes
  , edges: Map.fromFoldable $ map reduceEdge $ (Map.toUnfoldable graph.edges :: Array (Tuple node (Set node)))
  }
  where
    reduceEdge :: Tuple node (Set node) -> Tuple node (Set node)
    reduceEdge (Tuple source targets) =
      Tuple source (Set.filter (not <<< isTransitive source) targets)

    isTransitive :: node -> node -> Boolean
    isTransitive source target =
      let
        -- Get all intermediate nodes (direct targets except this one)
        intermediates = Set.delete target $ fromMaybe Set.empty $ Map.lookup source graph.edges

        -- Check if target is reachable through any intermediate
        reachableThroughIntermediate =
          Array.any (\intermediate ->
            Set.member target $ reachableFrom intermediate graph
          ) (Set.toUnfoldable intermediates)
      in
        reachableThroughIntermediate

-- | Get edges that were removed by transitive reduction
getRemovedEdges :: forall node. Ord node => SimpleGraph node -> SimpleGraph node -> Array (Tuple node node)
getRemovedEdges original reduced =
  let
    originalEdges = getAllEdges original
    reducedEdges = getAllEdges reduced
  in
    originalEdges \\ reducedEdges

-- | Get all edges from a graph as an array of tuples
getAllEdges :: forall node. Ord node => SimpleGraph node -> Array (Tuple node node)
getAllEdges graph =
  concat $ graph.nodes <#> \source ->
    case Map.lookup source graph.edges of
      Nothing -> []
      Just targets -> Set.toUnfoldable targets <#> \target ->
        Tuple source target

-- =============================================================================
-- || Conversion Utilities
-- =============================================================================

-- | Convert TaskNode array to SimpleGraph
taskNodesToSimpleGraph :: forall node. Ord node => Array (TaskNode node) -> SimpleGraph node
taskNodesToSimpleGraph tasks =
  { nodes: tasks <#> _.id
  , edges: Map.fromFoldable $ tasks <#> \task ->
      Tuple task.id (Set.fromFoldable task.depends)
  }

-- | Convert SimpleGraph to TaskNode array
simpleGraphToTaskNodes :: forall node. Ord node => SimpleGraph node -> Array (TaskNode node)
simpleGraphToTaskNodes graph =
  graph.nodes <#> \node ->
    { id: node
    , depends: case Map.lookup node graph.edges of
        Nothing -> []
        Just targets -> Set.toUnfoldable targets
    }

-- =============================================================================
-- || Cycle Detection
-- =============================================================================

-- | Check if a directed graph has a cycle using DFS with coloring
-- |
-- | Uses three colors:
-- | - White (unvisited)
-- | - Gray (currently in DFS stack)
-- | - Black (completely processed)
-- |
-- | A back edge to a gray node indicates a cycle.
hasCycle :: forall node. Ord node => SimpleGraph node -> Boolean
hasCycle graph = case findCycle graph of
  Nothing -> false
  Just _ -> true

-- | Find a cycle in the graph, if one exists
-- |
-- | Returns the nodes forming the cycle (in order).
findCycle :: forall node. Ord node => SimpleGraph node -> Maybe (Array node)
findCycle graph =
  let
    -- DFS state: white = unvisited, gray = in stack, black = done
    initialState = { white: Set.fromFoldable graph.nodes, gray: Set.empty, black: Set.empty, path: [], cycle: Nothing }

    result = foldl (\state node ->
      case state.cycle of
        Just _ -> state  -- Already found a cycle
        Nothing ->
          if Set.member node state.white
          then dfs state node
          else state
    ) initialState graph.nodes
  in result.cycle
  where
  dfs state node
    | Set.member node state.gray =
        -- Found a back edge - we have a cycle!
        -- Extract the cycle from path
        let cycleStart = Array.findIndex (_ == node) state.path
        in case cycleStart of
             Just idx -> state { cycle = Just (Array.drop idx state.path <> [node]) }
             Nothing -> state { cycle = Just [node] }
    | Set.member node state.black = state  -- Already fully processed
    | otherwise =
        let
          -- Move from white to gray
          state' = state
            { white = Set.delete node state.white
            , gray = Set.insert node state.gray
            , path = Array.snoc state.path node
            }
          -- Visit all neighbors
          neighbors = case Map.lookup node graph.edges of
            Nothing -> []
            Just targets -> Set.toUnfoldable targets
          state'' = foldl dfs state' neighbors
        in
          case state''.cycle of
            Just _ -> state''  -- Cycle found, propagate up
            Nothing ->
              -- Move from gray to black, remove from path
              state''
                { gray = Set.delete node state''.gray
                , black = Set.insert node state''.black
                , path = fromMaybe [] (Array.init state''.path)
                }

-- | Check if graph is a DAG (Directed Acyclic Graph)
isDAG :: forall node. Ord node => SimpleGraph node -> Boolean
isDAG = not <<< hasCycle

-- =============================================================================
-- || Connected Components
-- =============================================================================

-- | Find all connected components in an undirected graph
-- |
-- | Note: Treats the graph as undirected (ignores edge direction).
-- | Returns an array of sets, where each set is a connected component.
connectedComponents :: forall node. Ord node => SimpleGraph node -> Array (Set node)
connectedComponents graph =
  let
    -- Build undirected adjacency
    undirectedEdges = buildUndirectedEdges graph

    result = foldl (\{ visited, components } node ->
      if Set.member node visited
      then { visited, components }
      else
        let component = bfsComponent node undirectedEdges visited
        in { visited: Set.union visited component
           , components: Array.snoc components component
           }
    ) { visited: Set.empty, components: [] } graph.nodes
  in result.components
  where
  -- Build symmetric adjacency for undirected traversal
  buildUndirectedEdges :: SimpleGraph node -> Map node (Set node)
  buildUndirectedEdges g =
    foldl (\acc (Tuple src targets) ->
      let
        -- Add forward edges
        acc' = Map.alter (Just <<< Set.union targets <<< fromMaybe Set.empty) src acc
        -- Add reverse edges
        acc'' = foldl (\a tgt ->
          Map.alter (Just <<< Set.insert src <<< fromMaybe Set.empty) tgt a
        ) acc' (Set.toUnfoldable targets :: Array node)
      in acc''
    ) Map.empty (Map.toUnfoldable g.edges :: Array (Tuple node (Set node)))

  -- BFS to find all nodes in a component
  bfsComponent :: node -> Map node (Set node) -> Set node -> Set node
  bfsComponent start edges visited = go (Set.singleton start) (Set.singleton start)
    where
    go component frontier
      | Set.isEmpty frontier = component
      | otherwise =
          let
            neighbors = Set.unions $ Array.catMaybes $
              (Set.toUnfoldable frontier :: Array node) <#> \n -> Map.lookup n edges
            newNodes = Set.difference neighbors component
            newNodes' = Set.difference newNodes visited
          in go (Set.union component newNodes') newNodes'

-- | Check if the graph is connected (as undirected)
isConnected :: forall node. Ord node => SimpleGraph node -> Boolean
isConnected graph =
  case Array.head graph.nodes of
    Nothing -> true  -- Empty graph is connected
    Just _ ->
      let components = connectedComponents graph
      in Array.length components <= 1

-- =============================================================================
-- || Centrality Measures
-- =============================================================================

-- | Compute degree centrality for all nodes
-- |
-- | Degree centrality = (in-degree + out-degree) / (n - 1)
-- | where n is the number of nodes
degreeCentrality :: forall node. Ord node => SimpleGraph node -> Map node Number
degreeCentrality graph =
  let
    n = Array.length graph.nodes
    normalizer = if n <= 1 then 1.0 else toNumber (n - 1)
    inDegrees = inDegreeCentrality graph
    outDegrees = outDegreeCentrality graph
  in
    Map.fromFoldable $ graph.nodes <#> \node ->
      let
        inDeg = fromMaybe 0.0 $ Map.lookup node inDegrees
        outDeg = fromMaybe 0.0 $ Map.lookup node outDegrees
      in Tuple node ((inDeg + outDeg) * toNumber (n - 1) / normalizer)

-- | Compute in-degree centrality
-- |
-- | In-degree centrality = in-degree / (n - 1)
inDegreeCentrality :: forall node. Ord node => SimpleGraph node -> Map node Number
inDegreeCentrality graph =
  let
    n = Array.length graph.nodes
    normalizer = if n <= 1 then 1.0 else toNumber (n - 1)

    -- Count incoming edges for each node
    inDegrees = foldl (\acc (Tuple _ targets) ->
      foldl (\a tgt ->
        Map.alter (Just <<< (_ + 1) <<< fromMaybe 0) tgt a
      ) acc (Set.toUnfoldable targets :: Array node)
    ) (Map.fromFoldable $ graph.nodes <#> \n' -> Tuple n' 0)
      (Map.toUnfoldable graph.edges :: Array (Tuple node (Set node)))
  in
    map (\deg -> toNumber deg / normalizer) inDegrees

-- | Compute out-degree centrality
-- |
-- | Out-degree centrality = out-degree / (n - 1)
outDegreeCentrality :: forall node. Ord node => SimpleGraph node -> Map node Number
outDegreeCentrality graph =
  let
    n = Array.length graph.nodes
    normalizer = if n <= 1 then 1.0 else toNumber (n - 1)
  in
    Map.fromFoldable $ graph.nodes <#> \node ->
      let outDeg = case Map.lookup node graph.edges of
            Nothing -> 0
            Just targets -> Set.size targets
      in Tuple node (toNumber outDeg / normalizer)

-- =============================================================================
-- || Graph Metrics
-- =============================================================================

-- | Comprehensive metrics about a graph
type GraphMetrics =
  { nodeCount :: Int
  , edgeCount :: Int
  , density :: Number
  , averageDegree :: Number
  , isConnected :: Boolean
  , isDAG :: Boolean
  , componentCount :: Int
  }

-- | Compute all basic metrics for a graph
graphMetrics :: forall node. Ord node => SimpleGraph node -> GraphMetrics
graphMetrics graph =
  let
    nodeCount = Array.length graph.nodes
    edgeCount = Array.length (getAllEdges graph)
    components = connectedComponents graph
  in
    { nodeCount
    , edgeCount
    , density: density graph
    , averageDegree: averageDegree graph
    , isConnected: Array.length components <= 1
    , isDAG: isDAG graph
    , componentCount: Array.length components
    }

-- | Graph density: ratio of actual edges to possible edges
-- |
-- | For directed graphs: |E| / (|V| * (|V| - 1))
-- | Returns 0 for graphs with fewer than 2 nodes
density :: forall node. Ord node => SimpleGraph node -> Number
density graph =
  let
    n = Array.length graph.nodes
    e = Array.length (getAllEdges graph)
    maxEdges = n * (n - 1)
  in
    if maxEdges == 0
    then 0.0
    else toNumber e / toNumber maxEdges

-- | Average degree (in + out) per node
averageDegree :: forall node. Ord node => SimpleGraph node -> Number
averageDegree graph =
  let
    n = Array.length graph.nodes
    e = Array.length (getAllEdges graph)
  in
    if n == 0
    then 0.0
    else toNumber (2 * e) / toNumber n  -- Each edge contributes to 2 degrees

-- | Helper to convert Int to Number
toNumber :: Int -> Number
toNumber = Int.toNumber

-- =============================================================================
-- || Strongly Connected Components (Tarjan's Algorithm)
-- =============================================================================

-- | Find all strongly connected components using Tarjan's algorithm
-- |
-- | Returns components in reverse topological order (leaf components first).
-- | Each component is a set of nodes that are mutually reachable.
stronglyConnectedComponents :: forall node. Ord node => SimpleGraph node -> Array (Set node)
stronglyConnectedComponents graph =
  let
    initialState =
      { index: 0
      , stack: []
      , onStack: Set.empty
      , indices: Map.empty
      , lowlinks: Map.empty
      , sccs: []
      }

    result = foldl (\state node ->
      if Map.member node state.indices
      then state
      else tarjanDFS state node
    ) initialState graph.nodes
  in result.sccs
  where
  tarjanDFS :: TarjanState node -> node -> TarjanState node
  tarjanDFS state v =
    let
      -- Set the depth index and lowlink for v
      state' = state
        { index = state.index + 1
        , stack = Array.cons v state.stack
        , onStack = Set.insert v state.onStack
        , indices = Map.insert v state.index state.indices
        , lowlinks = Map.insert v state.index state.lowlinks
        }

      -- Get successors of v
      successors = case Map.lookup v graph.edges of
        Nothing -> []
        Just targets -> Set.toUnfoldable targets :: Array node

      -- Process all successors
      state'' = foldl (processSuccessor v) state' successors

      -- Get v's lowlink
      vLowlink = fromMaybe 0 $ Map.lookup v state''.lowlinks
      vIndex = fromMaybe 0 $ Map.lookup v state''.indices
    in
      if vLowlink == vIndex
      then popSCC state'' v
      else state''

  processSuccessor :: node -> TarjanState node -> node -> TarjanState node
  processSuccessor v state w =
    case Map.lookup w state.indices of
      Nothing ->
        -- w has not been visited; recurse
        let state' = tarjanDFS state w
            wLowlink = fromMaybe 0 $ Map.lookup w state'.lowlinks
            vLowlink = fromMaybe 0 $ Map.lookup v state'.lowlinks
        in state' { lowlinks = Map.insert v (min vLowlink wLowlink) state'.lowlinks }
      Just wIndex ->
        -- w is already visited
        if Set.member w state.onStack
        then
          -- w is on stack, so it's in the current SCC
          let vLowlink = fromMaybe 0 $ Map.lookup v state.lowlinks
          in state { lowlinks = Map.insert v (min vLowlink wIndex) state.lowlinks }
        else state

  popSCC :: TarjanState node -> node -> TarjanState node
  popSCC state v =
    let
      -- Pop nodes until we get to v
      result = popUntil state.stack v Set.empty
    in state
         { stack = result.remaining
         , onStack = foldl (flip Set.delete) state.onStack (Set.toUnfoldable result.scc :: Array node)
         , sccs = Array.snoc state.sccs result.scc
         }

  popUntil :: Array node -> node -> Set node -> { scc :: Set node, remaining :: Array node }
  popUntil stack target acc =
    case Array.uncons stack of
      Nothing -> { scc: acc, remaining: [] }
      Just { head, tail } ->
        let acc' = Set.insert head acc
        in if head == target
           then { scc: acc', remaining: tail }
           else popUntil tail target acc'

type TarjanState node =
  { index :: Int
  , stack :: Array node
  , onStack :: Set node
  , indices :: Map node Int
  , lowlinks :: Map node Int
  , sccs :: Array (Set node)
  }

-- | Check if a graph is a single SCC (strongly connected)
isSCC :: forall node. Ord node => SimpleGraph node -> Boolean
isSCC graph =
  let components = stronglyConnectedComponents graph
  in Array.length components == 1

-- =============================================================================
-- || PageRank
-- =============================================================================

-- | Configuration for PageRank algorithm
type PageRankConfig =
  { dampingFactor :: Number   -- Typically 0.85
  , iterations :: Int         -- Number of iterations
  , tolerance :: Number       -- Convergence tolerance
  }

-- | Default PageRank configuration
defaultPageRankConfig :: PageRankConfig
defaultPageRankConfig =
  { dampingFactor: 0.85
  , iterations: 100
  , tolerance: 1.0e-6
  }

-- | Compute PageRank scores for all nodes
-- |
-- | Uses the default configuration (damping factor 0.85, 100 iterations).
pageRank :: forall node. Ord node => SimpleGraph node -> Map node Number
pageRank = pageRankWithConfig defaultPageRankConfig

-- | Compute PageRank with custom configuration
pageRankWithConfig :: forall node. Ord node => PageRankConfig -> SimpleGraph node -> Map node Number
pageRankWithConfig config graph =
  let
    n = Array.length graph.nodes
    initialScore = if n == 0 then 0.0 else 1.0 / toNumber n
    initialRanks = Map.fromFoldable $ graph.nodes <#> \node -> Tuple node initialScore

    -- Precompute out-degrees for efficiency
    outDegrees = Map.fromFoldable $ graph.nodes <#> \node ->
      Tuple node $ case Map.lookup node graph.edges of
        Nothing -> 0
        Just targets -> Set.size targets

    -- Build reverse adjacency (who links to me?)
    reverseEdges = buildReverseEdges graph

    iterate :: Int -> Map node Number -> Map node Number
    iterate remaining ranks
      | remaining <= 0 = ranks
      | otherwise =
          let newRanks = computeNewRanks ranks
              converged = hasConverged ranks newRanks
          in if converged
             then newRanks
             else iterate (remaining - 1) newRanks

    computeNewRanks :: Map node Number -> Map node Number
    computeNewRanks ranks =
      Map.fromFoldable $ graph.nodes <#> \node ->
        let
          -- Get nodes that link to this node
          inLinks = fromMaybe Set.empty $ Map.lookup node reverseEdges

          -- Sum contributions from incoming links
          contribution = foldl (\acc source ->
            let sourceRank = fromMaybe 0.0 $ Map.lookup source ranks
                sourceOutDeg = fromMaybe 1 $ Map.lookup source outDegrees
            in acc + sourceRank / toNumber (max 1 sourceOutDeg)
          ) 0.0 (Set.toUnfoldable inLinks :: Array node)

          -- Apply damping formula
          newRank = (1.0 - config.dampingFactor) / toNumber n + config.dampingFactor * contribution
        in Tuple node newRank

    hasConverged :: Map node Number -> Map node Number -> Boolean
    hasConverged old new =
      let diff = foldl (\acc node ->
            let oldVal = fromMaybe 0.0 $ Map.lookup node old
                newVal = fromMaybe 0.0 $ Map.lookup node new
            in acc + Number.abs (newVal - oldVal)
          ) 0.0 graph.nodes
      in diff < config.tolerance
  in
    iterate config.iterations initialRanks

-- | Build reverse adjacency map (target -> set of sources)
buildReverseEdges :: forall node. Ord node => SimpleGraph node -> Map node (Set node)
buildReverseEdges graph =
  foldl (\acc (Tuple source targets) ->
    foldl (\a target ->
      Map.alter (Just <<< Set.insert source <<< fromMaybe Set.empty) target a
    ) acc (Set.toUnfoldable targets :: Array node)
  ) Map.empty (Map.toUnfoldable graph.edges :: Array (Tuple node (Set node)))

-- =============================================================================
-- || Community Detection (Label Propagation)
-- =============================================================================

-- | Community detection using label propagation
-- |
-- | Each node starts with its own label. In each iteration, nodes adopt
-- | the most common label among their neighbors. Returns a map from
-- | node to community label (using a representative node ID).
labelPropagation :: forall node. Ord node => SimpleGraph node -> Map node node
labelPropagation graph =
  let
    -- Initial labels: each node is its own community
    initialLabels = Map.fromFoldable $ graph.nodes <#> \n -> Tuple n n

    -- Build undirected neighbors
    undirectedNeighbors = buildUndirectedNeighbors graph

    -- Run iterations until convergence
    iterate :: Int -> Map node node -> Map node node
    iterate remaining labels
      | remaining <= 0 = labels
      | otherwise =
          let newLabels = propagateOnce labels
          in if labels == newLabels
             then labels
             else iterate (remaining - 1) newLabels

    propagateOnce :: Map node node -> Map node node
    propagateOnce labels =
      foldl (\acc node ->
        let neighbors = fromMaybe Set.empty $ Map.lookup node undirectedNeighbors
            neighborLabels = Array.catMaybes $
              (Set.toUnfoldable neighbors :: Array node) <#> \n ->
                Map.lookup n acc
            mostCommon = findMostCommon neighborLabels
            newLabel = case mostCommon of
              Nothing -> node  -- Keep own label if no neighbors
              Just l -> l
        in Map.insert node newLabel acc
      ) labels graph.nodes
  in
    iterate 100 initialLabels
  where
  buildUndirectedNeighbors :: SimpleGraph node -> Map node (Set node)
  buildUndirectedNeighbors g =
    foldl (\acc (Tuple src targets) ->
      let
        acc' = Map.alter (Just <<< Set.union targets <<< fromMaybe Set.empty) src acc
        acc'' = foldl (\a tgt ->
          Map.alter (Just <<< Set.insert src <<< fromMaybe Set.empty) tgt a
        ) acc' (Set.toUnfoldable targets :: Array node)
      in acc''
    ) Map.empty (Map.toUnfoldable g.edges :: Array (Tuple node (Set node)))

  findMostCommon :: Array node -> Maybe node
  findMostCommon labels =
    let counts = foldl (\acc l ->
          Map.alter (Just <<< (_ + 1) <<< fromMaybe 0) l acc
        ) Map.empty labels
        maxEntry = foldl (\best (Tuple label count) ->
          case best of
            Nothing -> Just (Tuple label count)
            Just (Tuple _ bestCount) ->
              if count > bestCount
              then Just (Tuple label count)
              else best
        ) Nothing (Map.toUnfoldable counts :: Array (Tuple node Int))
    in map (\(Tuple l _) -> l) maxEntry

-- | Compute modularity of a community assignment
-- |
-- | Modularity measures how good a community structure is.
-- | Higher values (max 1.0) indicate better community separation.
modularity :: forall node. Ord node => SimpleGraph node -> Map node node -> Number
modularity graph communities =
  let
    m = toNumber $ Array.length (getAllEdges graph)
    twoM = 2.0 * m

    result = foldl (\acc (Tuple source targets) ->
      let
        sourceCommunity = Map.lookup source communities
        sourceOutDeg = Set.size targets
        sourceInDeg = countInDegree source
      in foldl (\a target ->
           let
             targetCommunity = Map.lookup target communities
             targetOutDeg = case Map.lookup target graph.edges of
               Nothing -> 0
               Just t -> Set.size t
             targetInDeg = countInDegree target
             -- Add 1 if in same community (Kronecker delta)
             sameComm = if sourceCommunity == targetCommunity then 1.0 else 0.0
             -- Expected edges under null model
             expected = toNumber (sourceOutDeg + sourceInDeg) * toNumber (targetOutDeg + targetInDeg) / twoM
           in a + sameComm - expected
         ) acc (Set.toUnfoldable targets :: Array node)
    ) 0.0 (Map.toUnfoldable graph.edges :: Array (Tuple node (Set node)))
  in
    if m == 0.0 then 0.0 else result / twoM

  where
  countInDegree :: node -> Int
  countInDegree n =
    foldl (\acc (Tuple _ targets) ->
      if Set.member n targets then acc + 1 else acc
    ) 0 (Map.toUnfoldable graph.edges :: Array (Tuple node (Set node)))
