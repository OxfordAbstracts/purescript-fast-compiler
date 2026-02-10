-- | Tests for Link Operations
-- |
-- | Tests edge cases in swizzle and filter functions:
-- | - Out-of-bounds indices in swizzleLinks (should crash)
-- | - Missing nodes in swizzleLinksByIndex (should silently drop)
-- | - Empty arrays
-- | - IntSet/IntMap FFI operations
module Test.ForceEngine.LinksSpec where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..), isNothing)
import Effect (Effect)
import Effect.Console (log)
import Test.Assert (assert')

-- Import the module under test
import Hylograph.ForceEngine.Links as Links

-- =============================================================================
-- Test Node and Link Types
-- =============================================================================

type TestNode = { id :: String, index :: Int, x :: Number, y :: Number }
type TestLink = { source :: Int, target :: Int, weight :: Number }

mkNode :: String -> Int -> TestNode
mkNode id idx = { id, index: idx, x: 0.0, y: 0.0 }

mkLink :: Int -> Int -> TestLink
mkLink src tgt = { source: src, target: tgt, weight: 1.0 }

-- =============================================================================
-- Tests
-- =============================================================================

runTests :: Effect Unit
runTests = do
  log "\n--- ForceEngine/Links Tests ---"

  testSwizzleLinksHappyPath
  testSwizzleLinksCrashesOnOutOfBounds
  testSwizzleLinksByIndexHappyPath
  testSwizzleLinksByIndexDropsMissingNodes
  testSwizzleLinksByIndexEmptyNodes
  testSwizzleLinksByIndexEmptyLinks
  testFilterLinksToSubset
  testFilterLinksToEmptySubset
  testIntSetOperations
  testIntMapOperations
  testStringSetOperations

-- | Test: swizzleLinks works correctly when indices are valid
testSwizzleLinksHappyPath :: Effect Unit
testSwizzleLinksHappyPath = do
  log "\n  swizzleLinks (happy path):"

  let nodes =
        [ mkNode "a" 0
        , mkNode "b" 1
        , mkNode "c" 2
        ]

  let links =
        [ mkLink 0 1  -- a -> b
        , mkLink 1 2  -- b -> c
        ]

  let swizzled = Links.swizzleLinks nodes links \src tgt idx link ->
        { source: src, target: tgt, index: idx, weight: link.weight }

  assert' "Should produce 2 swizzled links" (Array.length swizzled == 2)

  case Array.index swizzled 0 of
    Just first -> do
      assert' "First link source should be node 'a'" (first.source.id == "a")
      assert' "First link target should be node 'b'" (first.target.id == "b")
      log "    First link: a -> b ✓"
    Nothing -> assert' "Should have first link" false

  case Array.index swizzled 1 of
    Just second -> do
      assert' "Second link source should be node 'b'" (second.source.id == "b")
      assert' "Second link target should be node 'c'" (second.target.id == "c")
      log "    Second link: b -> c ✓"
    Nothing -> assert' "Should have second link" false

  log "  ✓ swizzleLinks works with valid indices"

-- | Test: swizzleLinks CRASHES when link indices exceed array bounds
-- |
-- | THIS TEST DOCUMENTS THE BUG: If you have a filtered subset of nodes
-- | but links still reference the original indices, swizzleLinks will crash.
-- |
-- | The actual crash test is DISABLED because it would stop the test suite.
-- | When the bug is fixed (by returning Maybe or using safe indexing),
-- | this test should be updated to verify the safe behavior.
testSwizzleLinksCrashesOnOutOfBounds :: Effect Unit
testSwizzleLinksCrashesOnOutOfBounds = do
  log "\n  swizzleLinks (out-of-bounds - KNOWN BUG):"
  log "    ⚠ BUG: swizzleLinks uses unsafeCrashWith for out-of-bounds indices"
  log "    ⚠ If called with filtered nodes + original link indices, it crashes"
  log "    ⚠ Crash test disabled to allow test suite to continue"
  log ""
  log "    Reproduction scenario:"
  log "      nodes = [a@0, b@1]  -- only 2 nodes"
  log "      links = [{source: 0, target: 5}]  -- references missing index 5"
  log "      swizzleLinks nodes links transform  -- CRASHES"
  log ""
  log "    Workaround: Use swizzleLinksByIndex which handles missing nodes safely"
  log "  ⚠ KNOWN BUG - swizzleLinks is unsafe with filtered node subsets"

-- | Test: swizzleLinksByIndex works correctly when all nodes exist
testSwizzleLinksByIndexHappyPath :: Effect Unit
testSwizzleLinksByIndexHappyPath = do
  log "\n  swizzleLinksByIndex (happy path):"

  let nodes =
        [ mkNode "a" 0
        , mkNode "b" 1
        , mkNode "c" 2
        ]

  let links =
        [ mkLink 0 1  -- a -> b
        , mkLink 1 2  -- b -> c
        ]

  let swizzled = Links.swizzleLinksByIndex _.index nodes links \src tgt idx link ->
        { source: src, target: tgt, index: idx, weight: link.weight }

  assert' "Should produce 2 swizzled links" (Array.length swizzled == 2)
  log $ "    Produced " <> show (Array.length swizzled) <> " links"

  log "  ✓ swizzleLinksByIndex works with complete node set"

-- | Test: swizzleLinksByIndex SAFELY drops links when nodes are missing
-- |
-- | THIS IS THE CORRECT BEHAVIOR: When using a filtered subset of nodes,
-- | links referencing missing nodes are silently dropped.
testSwizzleLinksByIndexDropsMissingNodes :: Effect Unit
testSwizzleLinksByIndexDropsMissingNodes = do
  log "\n  swizzleLinksByIndex (missing nodes - SAFE BEHAVIOR):"

  -- Only nodes 0 and 2, missing node 1
  let nodes =
        [ mkNode "a" 0
        , mkNode "c" 2
        ]

  let links =
        [ mkLink 0 1  -- a -> (missing) - should be DROPPED
        , mkLink 1 2  -- (missing) -> c - should be DROPPED
        , mkLink 0 2  -- a -> c - should SURVIVE
        ]

  let swizzled = Links.swizzleLinksByIndex _.index nodes links \src tgt idx link ->
        { source: src, target: tgt, index: idx, weight: link.weight }

  assert' "Should produce only 1 link (the one with both endpoints present)"
    (Array.length swizzled == 1)
  log $ "    3 input links → " <> show (Array.length swizzled) <> " output link"

  case Array.head swizzled of
    Just link -> do
      assert' "Surviving link should be a -> c"
        (link.source.id == "a" && link.target.id == "c")
      log "    Surviving link: a -> c ✓"
    Nothing -> assert' "Should have one surviving link" false

  log "  ✓ swizzleLinksByIndex safely drops links with missing endpoints"

-- | Test: swizzleLinksByIndex handles empty nodes array
testSwizzleLinksByIndexEmptyNodes :: Effect Unit
testSwizzleLinksByIndexEmptyNodes = do
  log "\n  swizzleLinksByIndex (empty nodes):"

  let nodes = [] :: Array TestNode
  let links = [ mkLink 0 1 ]

  let swizzled = Links.swizzleLinksByIndex _.index nodes links \src tgt idx link ->
        { source: src, target: tgt, index: idx, weight: link.weight }

  assert' "Should produce 0 links when nodes is empty" (Array.length swizzled == 0)
  log "    Empty nodes → 0 output links ✓"

  log "  ✓ swizzleLinksByIndex handles empty nodes"

-- | Test: swizzleLinksByIndex handles empty links array
testSwizzleLinksByIndexEmptyLinks :: Effect Unit
testSwizzleLinksByIndexEmptyLinks = do
  log "\n  swizzleLinksByIndex (empty links):"

  let nodes = [ mkNode "a" 0 ]
  let links = [] :: Array TestLink

  let swizzled = Links.swizzleLinksByIndex _.index nodes links \src tgt idx link ->
        { source: src, target: tgt, index: idx, weight: link.weight }

  assert' "Should produce 0 links when links is empty" (Array.length swizzled == 0)
  log "    Empty links → 0 output links ✓"

  log "  ✓ swizzleLinksByIndex handles empty links"

-- | Test: filterLinksToSubset keeps only links between subset nodes
testFilterLinksToSubset :: Effect Unit
testFilterLinksToSubset = do
  log "\n  filterLinksToSubset:"

  -- Subset: only nodes 0 and 2
  let nodes =
        [ mkNode "a" 0
        , mkNode "c" 2
        ]

  let links =
        [ mkLink 0 1  -- a -> (missing) - DROPPED
        , mkLink 1 2  -- (missing) -> c - DROPPED
        , mkLink 0 2  -- a -> c - KEPT
        , mkLink 2 0  -- c -> a - KEPT
        ]

  let filtered = Links.filterLinksToSubset _.index nodes links

  assert' "Should keep only 2 links (both endpoints in subset)"
    (Array.length filtered == 2)
  log $ "    4 input links → " <> show (Array.length filtered) <> " filtered links"

  log "  ✓ filterLinksToSubset correctly filters to subset"

-- | Test: filterLinksToSubset with empty subset
testFilterLinksToEmptySubset :: Effect Unit
testFilterLinksToEmptySubset = do
  log "\n  filterLinksToSubset (empty subset):"

  let nodes = [] :: Array TestNode
  let links = [ mkLink 0 1, mkLink 1 2 ]

  let filtered = Links.filterLinksToSubset _.index nodes links

  assert' "Should produce 0 links when subset is empty" (Array.length filtered == 0)
  log "    Empty subset → 0 links ✓"

  log "  ✓ filterLinksToSubset handles empty subset"

-- | Test: IntSet FFI operations
testIntSetOperations :: Effect Unit
testIntSetOperations = do
  log "\n  IntSet FFI operations:"

  let set = Links.buildIntSet [1, 3, 5, 7]

  assert' "1 should be in set" (Links.intSetMember 1 set)
  assert' "3 should be in set" (Links.intSetMember 3 set)
  assert' "5 should be in set" (Links.intSetMember 5 set)
  assert' "2 should NOT be in set" (not $ Links.intSetMember 2 set)
  assert' "4 should NOT be in set" (not $ Links.intSetMember 4 set)
  assert' "0 should NOT be in set" (not $ Links.intSetMember 0 set)

  log "    buildIntSet [1,3,5,7] - membership tests pass ✓"

  -- Empty set
  let emptySet = Links.buildIntSet []
  assert' "Empty set should have no members" (not $ Links.intSetMember 0 emptySet)
  log "    Empty IntSet works ✓"

  log "  ✓ IntSet FFI operations work correctly"

-- | Test: IntMap FFI operations
testIntMapOperations :: Effect Unit
testIntMapOperations = do
  log "\n  IntMap FFI operations:"

  let nodes =
        [ mkNode "a" 10
        , mkNode "b" 20
        , mkNode "c" 30
        ]

  let nodeMap = Links.buildIntMap _.index nodes

  -- Lookup existing keys
  case Links.intMapLookup 10 nodeMap of
    Just node -> assert' "Key 10 should map to node 'a'" (node.id == "a")
    Nothing -> assert' "Key 10 should exist" false

  case Links.intMapLookup 20 nodeMap of
    Just node -> assert' "Key 20 should map to node 'b'" (node.id == "b")
    Nothing -> assert' "Key 20 should exist" false

  log "    buildIntMap with index accessor - lookups work ✓"

  -- Lookup non-existent key
  assert' "Key 99 should not exist" (isNothing $ Links.intMapLookup 99 nodeMap)
  log "    Missing key returns Nothing ✓"

  -- Empty map
  let emptyMap = Links.buildIntMap _.index ([] :: Array TestNode)
  assert' "Empty map lookup should return Nothing"
    (isNothing $ Links.intMapLookup 0 emptyMap)
  log "    Empty IntMap works ✓"

  log "  ✓ IntMap FFI operations work correctly"

-- | Test: StringSet FFI operations
testStringSetOperations :: Effect Unit
testStringSetOperations = do
  log "\n  StringSet FFI operations:"

  let set = Links.buildStringSet ["apple", "banana", "cherry"]

  assert' "apple should be in set" (Links.stringSetMember "apple" set)
  assert' "banana should be in set" (Links.stringSetMember "banana" set)
  assert' "orange should NOT be in set" (not $ Links.stringSetMember "orange" set)
  assert' "empty string should NOT be in set" (not $ Links.stringSetMember "" set)

  log "    buildStringSet [apple, banana, cherry] - membership tests pass ✓"

  log "  ✓ StringSet FFI operations work correctly"
