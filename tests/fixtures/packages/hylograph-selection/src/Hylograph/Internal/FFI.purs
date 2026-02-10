-- | Internal: Low-level FFI bindings for D3 selection and simulation.
-- |
-- | This module contains the JavaScript FFI declarations for:
-- | - Selection operations (events, key functions)
-- | - Simulation lifecycle (init, start, stop, tick)
-- | - Force configuration (center, collide, many-body, link, radial, x, y)
-- | - Node/link manipulation (pin, unpin, swizzle)
-- |
-- | **Internal module** - prefer the high-level APIs in `Hylograph.Selection`
-- | and `Hylograph.Simulation`.
module Hylograph.Internal.FFI
  ( -- Selection FFI (legacy - most selection ops now use web-dom)
    getIndexFromDatum_
  , ComputeKeyFunction_
  , keyIsID_
  , keyIsSourceTarget_
  , swizzledLinkKey_
  , D3Attr_
  , selectionOn_
  -- NOTE: D3DragFunction_, simulationDrag_, simdrag_, simdragHorizontal_, disableDrag_
  -- REMOVED - use PSD3.Interaction.Pointer for native Pointer Events drag
  -- Simulation FFI
  , linksForceName_
  , GraphModel_
  , D3ForceHandle_
  , CustomForceConfig_
  , SimulationVariables
  , initSimulation_
  , configSimulation_
  , readSimulationVariables_
  , d3PreserveSimulationPositions_
  , d3PreserveLinkReferences_
  , getIDsFromNodes_
  , getNodes_
  , setNodes_
  , setLinks_
  , swizzleLinks_
  , getLinkID_
  , getLinkIDs_
  , unsetLinks_
  , getLinksFromForce_
  , getLinksFromSimulation_
  , startSimulation_
  , stopSimulation_
  , setInSimNodeFlag_
  , unsetInSimNodeFlag_
  , setInSimNodeFlag
  , unsetInSimNodeFlag
  , pinNode_
  , pinNamedNode_
  , pinTreeNode_
  , unpinNode_
  , onTick_
  , disableTick_
  , defaultNodeTick_
  , defaultLinkTick_
  , setAlpha_
  , setAlphaMin_
  , setAlphaDecay_
  , setAlphaTarget_
  , setVelocityDecay_
  -- Force FFI
  , forceCenter_
  , forceCollideFn_
  , forceMany_
  , forceRadial_
  , forceX_
  , forceY_
  , forceLink_
  , forceCustom_
  , dummyForceHandle_
  , setForceRadius_
  , setForceStrength_
  , setForceCx_
  , setForceCy_
  , setForceTheta_
  , setForceDistanceMin_
  , setForceDistanceMax_
  , setForceIterations_
  , setForceX_
  , setForceY_
  , setForceDistance_
  , setLinksKeyFunction_
  , putForceInSimulation_
  , lookupForceByName_
  , removeFixForceXY_
  , removeFixForceX_
  , removeFixForceY_
  , applyFixForceInSimulationXY_
  , applyFixForceInSimulationX_
  , applyFixForceInSimulationY_
  , setAsNullForceInSimulation_
  -- Arc generator FFI (from d3-shape, for pie/donut charts)
  , ArcGenerator_
  , arcGenerator_
  , arcPath_
  , setArcInnerRadius_
  , setArcOuterRadius_
  ) where

-- brings together ALL of the wrapped D3js functions and FFI / native types
-- probably should break it up again when it's more feature complete (ie to match D3 modules). Maybe.

import Hylograph.Data.Node

import Hylograph.Internal.Types (D3Selection_, D3Simulation_, Datum_, Index_, PointXY)
import Data.Nullable (Nullable)
import Prelude (Unit)

-- | *********************************************************************************************************************
-- | ***************************   FFI signatures for Selection                ********************************************
-- | *********************************************************************************************************************
-- | NOTE: Most D3 selection operations have been replaced with PureScript web-dom libraries.
-- | The remaining exports here are for simulation key functions and drag behaviors.

foreign import getIndexFromDatum_    :: Datum_ -> Int

type ComputeKeyFunction_ d key = d -> key
foreign import keyIsID_           :: forall d. ComputeKeyFunction_ d Index_
foreign import keyIsSourceTarget_ :: forall d. ComputeKeyFunction_ d Index_ -- used for links in simulation
foreign import swizzledLinkKey_   :: forall d. ComputeKeyFunction_ d String -- key function for swizzled links (extracts source/target IDs)

-- D3Attr_ is used by force configuration functions
foreign import data D3Attr_ :: Type

-- NOTE: D3DragFunction_ and drag functions REMOVED
-- Use PSD3.Interaction.Pointer for native Pointer Events drag

foreign import selectionOn_         :: forall selection callback. selection -> String -> callback -> selection  


-- | *********************************************************************************************************************
-- | ***************************   FFI signatures for D3js Simulation module  *********************************************
-- | *********************************************************************************************************************

-- links force is very special, can't (easily) manage multiple named versions. 
-- consistency of naming of link force is established with top level name
foreign import linksForceName_ :: String

-- | foreign types associated with Force Layout Simulation
type GraphModel_ link node = { links :: Array link, nodes :: Array node }
foreign import data D3ForceHandle_     :: Type
foreign import data CustomForceConfig_ :: Type

-- | a record to initialize / configure simulations
type SimulationVariables = { 
      alpha         :: Number
    , alphaTarget   :: Number
    , alphaMin      :: Number
    , alphaDecay    :: Number
    , velocityDecay :: Number
}

foreign import initSimulation_         :: forall d key.    SimulationVariables -> (SimulationNode d -> key) -> D3Simulation_
foreign import configSimulation_       :: D3Simulation_ -> SimulationVariables -> D3Simulation_
foreign import readSimulationVariables_ :: D3Simulation_ -> SimulationVariables

foreign import d3PreserveSimulationPositions_ ::
  forall d row key.
  D3Selection_ d ->
  Array (SimulationNode row) ->
  (SimulationNode row -> key) ->
  Array (SimulationNode row)
foreign import d3PreserveLinkReferences_ ::
  forall d id linkRow.
  D3Selection_ d ->
  Array (Link id linkRow) ->
  Array (Link id linkRow)

foreign import getIDsFromNodes_ :: forall d key. Array (SimulationNode d) -> (SimulationNode d -> key) -> Array key

foreign import getNodes_ :: forall d.   D3Simulation_ -> Array (SimulationNode d)
foreign import setNodes_ :: forall d.   D3Simulation_ -> Array (SimulationNode d) -> Array (SimulationNode d)
-- setLinks will do the swizzling AND prune any links that have source or target that is not in [nodes]
foreign import setLinks_ ::
  forall nodeData linkRow.
  D3Simulation_ ->
  Array (SwizzledLink nodeData linkRow) ->
  Unit
foreign import swizzleLinks_ ::
  forall id nodeData linkRow key.
  Array (Link id linkRow) ->
  Array (SimulationNode nodeData) ->
  (SimulationNode nodeData -> key) ->
  Array (SwizzledLink nodeData linkRow)

foreign import getLinkID_              :: forall link key. (link -> key) -> link -> Index_
foreign import getLinkIDs_             :: forall id linkRow. Link id linkRow -> { sourceID :: id, targetID :: id }
foreign import unsetLinks_             :: D3Simulation_ -> D3Simulation_

foreign import getLinksFromForce_      :: forall id linkRow. D3ForceHandle_ -> Array (Link id linkRow)
foreign import getLinksFromSimulation_ :: forall nodeData linkRow. D3Simulation_ -> Array (SwizzledLink nodeData linkRow)

foreign import startSimulation_        :: D3Simulation_ -> Unit
foreign import stopSimulation_         :: D3Simulation_ -> Unit

foreign import setInSimNodeFlag_     :: forall d. SimulationNode d -> Unit
foreign import unsetInSimNodeFlag_   :: forall d. SimulationNode d -> Unit

-- following functions modify the node and return it - meant to be used on staged data which will then be re-entered to sim
foreign import pinNode_              :: forall d. Number -> Number -> SimulationNode d -> SimulationNode d
foreign import pinNamedNode_         :: forall d. String -> Number -> Number -> SimulationNode d -> SimulationNode d
foreign import pinTreeNode_          :: forall d. SimulationNode d -> SimulationNode d -- modifies fx/fy
foreign import unpinNode_            :: forall d. SimulationNode d -> SimulationNode d -- set fx/fy to null

-- NB mutating function
-- pinNode :: forall d. SimulationNode d -> PointXY -> SimulationNode d
-- pinNode node p = do
--   let _ = pinNode_ p.x p.y node
--   node -- NB mutated value, fx / fy have been set
-- NB mutating function
setInSimNodeFlag :: forall d. SimulationNode d -> SimulationNode d
setInSimNodeFlag node = do
  let _ = setInSimNodeFlag_ node
  node -- NB mutated value, inSim now true
unsetInSimNodeFlag :: forall d. SimulationNode d -> SimulationNode d
unsetInSimNodeFlag node = do
  let _ = unsetInSimNodeFlag_ node
  node -- NB mutated value, inSim now false

foreign import onTick_                :: D3Simulation_ -> String -> (Unit -> Unit) -> Unit
foreign import disableTick_           :: D3Simulation_ -> String -> Unit
foreign import defaultNodeTick_       :: forall d. String -> D3Simulation_ -> D3Selection_ d -> Unit
foreign import defaultLinkTick_       :: forall d. String -> D3Simulation_ -> D3Selection_ d -> Unit
foreign import setAlpha_              :: D3Simulation_ -> Number -> Unit
foreign import setAlphaMin_           :: D3Simulation_ -> Number -> Unit
foreign import setAlphaDecay_         :: D3Simulation_ -> Number -> Unit
foreign import setAlphaTarget_        :: D3Simulation_ -> Number -> Unit
foreign import setVelocityDecay_      :: D3Simulation_ -> Number -> Unit

-- implementations / wrappers for the Force ADT
foreign import forceCenter_       :: Unit -> D3ForceHandle_
foreign import forceCollideFn_    :: Unit -> D3ForceHandle_
foreign import forceMany_         :: Unit -> D3ForceHandle_
foreign import forceRadial_       :: Unit -> D3ForceHandle_
foreign import forceX_            :: Unit -> D3ForceHandle_
foreign import forceY_            :: Unit -> D3ForceHandle_
foreign import forceLink_         :: Unit -> D3ForceHandle_ -- actually created in initSimulation where keyFunction is provided too
foreign import forceCustom_       :: Unit -> D3ForceHandle_
foreign import dummyForceHandle_  :: D3ForceHandle_ -- used for fixed "forces", is null under the hood

foreign import setForceRadius_      :: D3ForceHandle_ -> D3Attr_ -> D3ForceHandle_
foreign import setForceStrength_    :: D3ForceHandle_ -> D3Attr_ -> D3ForceHandle_
foreign import setForceCx_          :: D3ForceHandle_ -> D3Attr_ -> D3ForceHandle_
foreign import setForceCy_          :: D3ForceHandle_ -> D3Attr_ -> D3ForceHandle_
foreign import setForceTheta_       :: D3ForceHandle_ -> D3Attr_ -> D3ForceHandle_
foreign import setForceDistanceMin_ :: D3ForceHandle_ -> D3Attr_ -> D3ForceHandle_
foreign import setForceDistanceMax_ :: D3ForceHandle_ -> D3Attr_ -> D3ForceHandle_
foreign import setForceIterations_  :: D3ForceHandle_ -> D3Attr_ -> D3ForceHandle_
foreign import setForceX_           :: D3ForceHandle_ -> D3Attr_ -> D3ForceHandle_
foreign import setForceY_           :: D3ForceHandle_ -> D3Attr_ -> D3ForceHandle_
foreign import setForceDistance_    :: D3ForceHandle_ -> D3Attr_ -> D3ForceHandle_
foreign import setLinksKeyFunction_ :: D3ForceHandle_ -> D3Attr_ -> D3ForceHandle_

foreign import putForceInSimulation_        :: D3Simulation_ -> String -> D3ForceHandle_ -> D3Simulation_
foreign import lookupForceByName_           :: D3Simulation_ -> String -> Nullable D3ForceHandle_
foreign import removeFixForceXY_            :: D3Simulation_ -> (Datum_ -> Boolean) -> D3Simulation_
foreign import removeFixForceX_             :: D3Simulation_ -> (Datum_ -> Boolean) -> D3Simulation_
foreign import removeFixForceY_             :: D3Simulation_ -> (Datum_ -> Boolean) -> D3Simulation_
foreign import applyFixForceInSimulationXY_ :: D3Simulation_ -> String -> (Datum_ -> Index_ -> PointXY) -> (Datum_ -> Boolean) -> D3Simulation_ 
foreign import applyFixForceInSimulationX_  :: D3Simulation_ -> String -> (Datum_ -> Index_ -> { x :: Number})  -> (Datum_ -> Boolean) -> D3Simulation_ 
foreign import applyFixForceInSimulationY_  :: D3Simulation_ -> String -> (Datum_ -> Index_ -> { y :: Number})  -> (Datum_ -> Boolean) -> D3Simulation_ 
foreign import setAsNullForceInSimulation_  :: D3Simulation_ -> String -> D3Simulation_

-- | *********************************************************************************************************************
-- | ***************************   FFI signatures for D3js Arc Generator (d3-shape)      *********************************
-- | *********************************************************************************************************************
-- | Used for pie charts, donut charts, and other arc-based visualizations
foreign import data ArcGenerator_ :: Type

foreign import arcGenerator_           :: Unit -> ArcGenerator_
foreign import arcPath_                :: ArcGenerator_ -> Datum_ -> String
foreign import setArcInnerRadius_      :: ArcGenerator_ -> Number -> ArcGenerator_
foreign import setArcOuterRadius_      :: ArcGenerator_ -> Number -> ArcGenerator_
