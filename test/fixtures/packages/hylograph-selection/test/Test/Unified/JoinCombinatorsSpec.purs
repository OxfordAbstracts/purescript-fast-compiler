-- | Test.Unified.JoinCombinatorsSpec
-- |
-- | Tests for the new composable join combinators.
-- | Verifies that joins built with the new combinators produce
-- | correct AST structures via the Mermaid interpreter.
module Test.Unified.JoinCombinatorsSpec where

import Prelude hiding (join, (>>>))

import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Console (log)

-- AST and Elements
import Hylograph.AST (Tree, elem)
import Hylograph.Internal.Selection.Types (ElementType(..))

-- New Join Combinators
import Hylograph.Unified.Join as J

-- Display and Attributes
import Hylograph.Unified.Display as D
import Hylograph.Unified.Display ((>>>))
import Hylograph.Unified.Attribute (attr, attrStatic)

-- Mermaid interpreter for structure verification
import Hylograph.Interpreter.Mermaid (runMermaidTree)

-- =============================================================================
-- Test Data Types
-- =============================================================================

type DataPoint =
  { x :: Number
  , y :: Number
  , value :: Number
  , label :: String
  }

type SceneData =
  { name :: String
  , points :: Array DataPoint
  }

-- =============================================================================
-- Test Data
-- =============================================================================

testPoints :: Array DataPoint
testPoints =
  [ { x: 10.0, y: 20.0, value: 5.0, label: "A" }
  , { x: 30.0, y: 40.0, value: 8.0, label: "B" }
  , { x: 50.0, y: 60.0, value: 3.0, label: "C" }
  ]

testScene :: SceneData
testScene =
  { name: "Test Scene"
  , points: testPoints
  }

-- =============================================================================
-- Join Combinator Tests
-- =============================================================================

-- | Test 1: Basic join (no decompose, no GUP)
-- | Should produce a Join constructor in the AST
basicJoinTree :: Tree DataPoint
basicJoinTree =
  J.join "circles" "circle" testPoints _.label circleTemplate
    # J.toTree
  where
  circleTemplate :: DataPoint -> Tree DataPoint
  circleTemplate _ = elem Circle
    [ attr "cx" _.x D.showNumD
    , attr "cy" _.y D.showNumD
    , attr "r" _.value D.showNumD
    , attrStatic "fill" "steelblue"
    ]

-- | Test 2: Join with GUP (enter/update/exit)
-- | Should produce an UpdateJoin constructor in the AST
gupJoinTree :: Tree DataPoint
gupJoinTree =
  J.join "bars" "rect" testPoints _.label rectTemplate
    # J.withGUP gupSpec
    # J.toTree
  where
  rectTemplate :: DataPoint -> Tree DataPoint
  rectTemplate _ = elem Rect
    [ attr "x" _.x D.showNumD
    , attr "y" _.y D.showNumD
    , attr "width" (const 20.0) D.showNumD
    , attr "height" _.value (D.scaleD 10.0 >>> D.showNumD)
    ]
  gupSpec =
    { enter: Just $ J.enterSpec
        [ attr "opacity" (const 0.0) D.showNumD
        , attr "height" (const 0.0) D.showNumD
        ]
        Nothing
    , update: Just $ J.updateSpec [] Nothing
    , exit: Just $ J.exitSpec
        [ attr "opacity" (const 0.0) D.showNumD ]
        Nothing
    }

-- | Test 3: Nested join (with decomposition)
-- | Should produce a NestedJoin constructor in the AST
nestedJoinTree :: Tree SceneData
nestedJoinTree =
  J.nestedJoin "points" "circle" [testScene] _.points _.label circleTemplate
    # J.toTree
  where
  circleTemplate :: DataPoint -> Tree DataPoint
  circleTemplate _ = elem Circle
    [ attr "cx" _.x D.showNumD
    , attr "cy" _.y D.showNumD
    , attr "r" _.value D.showNumD
    ]

-- | Test 4: Full join (decomposition + GUP)
-- | Should produce an UpdateNestedJoin constructor in the AST
fullJoinTree :: Tree SceneData
fullJoinTree =
  J.fullJoin "viz" "circle" [testScene] _.points _.label circleTemplate gupSpec
    # J.toTree
  where
  circleTemplate :: DataPoint -> Tree DataPoint
  circleTemplate _ = elem Circle
    [ attr "cx" _.x D.showNumD
    , attr "cy" _.y D.showNumD
    , attr "r" _.value (D.clampD 2.0 20.0 >>> D.showNumD)
    , attrStatic "fill" "coral"
    ]
  gupSpec =
    { enter: Just $ J.noTransition
        [ attr "r" (const 0.0) D.showNumD
        , attr "opacity" (const 0.0) D.showNumD
        ]
    , update: Nothing
    , exit: Just $ J.noTransition
        [ attr "opacity" (const 0.0) D.showNumD ]
    }

-- | Test 5: Using convenience function basicJoin
basicJoinConvenienceTree :: Tree DataPoint
basicJoinConvenienceTree =
  J.basicJoin "dots" "circle" testPoints _.label dotTemplate
    # J.toTree
  where
  dotTemplate :: DataPoint -> Tree DataPoint
  dotTemplate _ = elem Circle
    [ attr "cx" _.x D.showNumD
    , attr "cy" _.y D.showNumD
    , attrStatic "r" "5"
    ]

-- | Test 6: Using gupJoin convenience function
gupJoinConvenienceTree :: Tree DataPoint
gupJoinConvenienceTree =
  J.gupJoin "animated" "circle" testPoints _.label circleTemplate gup
    # J.toTree
  where
  circleTemplate :: DataPoint -> Tree DataPoint
  circleTemplate _ = elem Circle
    [ attr "cx" _.x D.showNumD
    , attr "cy" _.y D.showNumD
    , attr "r" _.value D.showNumD
    ]
  gup =
    { enter: Just $ J.noTransition [ attr "r" (const 0.0) D.showNumD ]
    , update: Nothing
    , exit: Just $ J.noTransition [ attr "opacity" (const 0.0) D.showNumD ]
    }

-- =============================================================================
-- Run Tests
-- =============================================================================

runTests :: Effect Unit
runTests = do
  log "\n=== Join Combinators Tests ==="

  log "\n--- Test 1: Basic Join ---"
  log "join \"circles\" \"circle\" data template # toTree"
  log "Expected: Join constructor"
  mermaid1 <- runMermaidTree basicJoinTree
  log $ "Mermaid:\n" <> mermaid1

  log "\n--- Test 2: Join with GUP ---"
  log "join \"bars\" \"rect\" data template # withGUP gup # toTree"
  log "Expected: UpdateJoin constructor"
  mermaid2 <- runMermaidTree gupJoinTree
  log $ "Mermaid:\n" <> mermaid2

  log "\n--- Test 3: Nested Join ---"
  log "nestedJoin \"points\" \"circle\" [scene] _.points template # toTree"
  log "Expected: NestedJoin constructor"
  mermaid3 <- runMermaidTree nestedJoinTree
  log $ "Mermaid:\n" <> mermaid3

  log "\n--- Test 4: Full Join (decompose + GUP) ---"
  log "fullJoin \"viz\" \"circle\" [scene] _.points template gup # toTree"
  log "Expected: UpdateNestedJoin constructor"
  mermaid4 <- runMermaidTree fullJoinTree
  log $ "Mermaid:\n" <> mermaid4

  log "\n--- Test 5: basicJoin convenience ---"
  log "basicJoin \"dots\" \"circle\" data template # toTree"
  log "Expected: Join constructor (same as Test 1)"
  mermaid5 <- runMermaidTree basicJoinConvenienceTree
  log $ "Mermaid:\n" <> mermaid5

  log "\n--- Test 6: gupJoin convenience ---"
  log "gupJoin \"animated\" \"circle\" data template gup # toTree"
  log "Expected: UpdateJoin constructor (same as Test 2)"
  mermaid6 <- runMermaidTree gupJoinConvenienceTree
  log $ "Mermaid:\n" <> mermaid6

  log "\n=== All Join Combinator Tests Complete ==="
