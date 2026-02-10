-- | Hylograph.Render - Core rendering API for visualization ASTs
-- |
-- | This module provides the essential functions for rendering AST specifications
-- | to the DOM via D3.js.
-- |
-- | ## Usage
-- |
-- | ```purescript
-- | import Hylograph.AST as A
-- | import Hylograph.Render (runD3, select, renderTree)
-- |
-- | main :: Effect Unit
-- | main = void $ runD3 do
-- |   container <- select "#chart"
-- |   renderTree container myAST
-- | ```
-- |
module Hylograph.Render
  ( -- * D3 Monad
    runD3
  , D3M
  , D3Selection
    -- * Selection Operations
  , selectChildInheriting
    -- * Re-exports: Selection Operations
  , module SelectionExports
    -- * Re-exports: D3 Interpreter
  , module D3Exports
  ) where

import Prelude

import Effect (Effect)

import Hylograph.Interpreter.D3 (D3v2M, D3v2Selection_, runD3v2M, reselectD3v2, selectChildInheritingD3v2) as D3Exports
import Hylograph.Internal.Capabilities.Selection (select, selectAll, selectAllWithData, renderTree, renderData, setAttrs, clear) as SelectionExports
import Hylograph.Internal.Selection.Types (SBoundOwns)
import Web.DOM.Element (Element)

-- | Type alias for the D3 monad
type D3M = D3Exports.D3v2M

-- | Type alias for D3 selections
type D3Selection = D3Exports.D3v2Selection_

-- | Run a D3 computation (alias for runD3v2M)
runD3 :: D3M ~> Effect
runD3 = D3Exports.runD3v2M

-- | Select child elements, inheriting parent's data
-- | Alias for selectChildInheritingD3v2 for convenient import
selectChildInheriting
  :: forall parent datum
   . String
  -> D3Exports.D3v2Selection_ SBoundOwns parent datum
  -> D3Exports.D3v2M (D3Exports.D3v2Selection_ SBoundOwns Element datum)
selectChildInheriting = D3Exports.selectChildInheritingD3v2
