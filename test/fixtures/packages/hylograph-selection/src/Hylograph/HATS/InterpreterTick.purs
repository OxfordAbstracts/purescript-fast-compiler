-- | HATS Tick-Driven Interpreter
-- |
-- | Renders HATS trees to DOM with tick-driven transitions.
-- |
-- | This interpreter works with the unparameterized Tree type where:
-- | - Folds are existentially wrapped (SomeFold)
-- | - Attributes and behaviors are thunks that captured their values
module Hylograph.HATS.InterpreterTick
  ( rerender
  , rerenderInto
  , clearContainer
  , RerenderResult
  , SelectionMap
  ) where

import Prelude

import Data.Array as Array
import Data.Int (toNumber)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (unwrap)
import Data.Set as Set
import Data.Time.Duration (Milliseconds(..))
import Data.Foldable (traverse_)
import Data.Traversable (traverse)
import Data.TraversableWithIndex (traverseWithIndex)
import Effect (Effect)

import Hylograph.HATS (Tree(..), SomeFold, runSomeFold, Enumeration(..), Assembly(..), TraversalOrder(..), Attr(..), ThunkedBehavior(..), GUPSpec, PhaseSpec)
import Hylograph.HATS.Transitions (HATSTransitions(..), ElementTransitions, AttrTransition, toTickEasing)
import Hylograph.Internal.Behavior.Types (DragConfig(..), ZoomConfig(..), ScaleExtent(..), HighlightClass(..), TooltipTrigger(..))
import Hylograph.Internal.Behavior.Types (HighlightClass(..)) as HC
import Hylograph.Interaction.Coordinated (InteractionState(..), InteractionTrigger(..), BoundingBox)
import Hylograph.Interaction.Coordinated (InteractionState(..)) as IS
import Hylograph.Internal.Selection.Types (ElementType(..))
import Hylograph.Internal.Selection.Operations (createElementWithNS)
import Web.DOM.Element (Element)
import Web.DOM.Element (toNode) as Element
import Web.DOM.Node (appendChild) as Node
import Web.DOM.Document (Document)
import Web.HTML (window)
import Web.HTML.Window (document)
import Web.HTML.HTMLDocument as HTMLDocument
import Data.Number as Number
import Data.Nullable (Nullable, toNullable)

-- | Selection map - named selections for later access
type SelectionMap = Map String (Array Element)

-- | Result of rerender - selections plus optional transitions to tick
type RerenderResult =
  { selections :: SelectionMap
  , transitions :: Maybe HATSTransitions
  }

-- | Internal result type that accumulates transitions during interpretation
type InterpResult =
  { selections :: SelectionMap
  , entering :: Array (Array ElementTransitions)
  , updating :: Array (Array ElementTransitions)
  , exiting :: Array (Array ElementTransitions)
  }

-- | Result of processing a tree node - tracks how many DOM elements were created
type ProcessResult = { result :: InterpResult, elementsCreated :: Int }

-- | Re-render a HATS tree with GUP, returning tick-driven transitions
-- |
-- | Note: Tree has no type parameter - it composes freely
rerender :: String -> Tree -> Effect RerenderResult
rerender selector tree = do
  doc <- window >>= document >>= pure <<< HTMLDocument.toDocument
  container <- selectElement selector doc
  rerenderTree doc container tree

-- | Clear all children from a container
clearContainer :: String -> Effect Unit
clearContainer selector = do
  doc <- window >>= document >>= pure <<< HTMLDocument.toDocument
  container <- selectElement selector doc
  children <- getChildElements container
  traverse_ removeElement children

-- | Re-render into a named selection from a previous render
rerenderInto :: SelectionMap -> String -> Tree -> Effect RerenderResult
rerenderInto selections name tree = do
  doc <- window >>= document >>= pure <<< HTMLDocument.toDocument
  case Map.lookup name selections of
    Nothing -> pure { selections: Map.empty, transitions: Nothing }
    Just elements -> case Array.head elements of
      Nothing -> pure { selections: Map.empty, transitions: Nothing }
      Just container -> rerenderTree doc container tree

-- | The GUP-aware interpreter with tick-driven transitions
rerenderTree :: Document -> Element -> Tree -> Effect RerenderResult
rerenderTree doc parent tree = do
  { result } <- goWithDomIdx parent 0 tree
  let allEntering = Array.concat result.entering
  let allUpdating = Array.concat result.updating
  let allExiting = Array.concat result.exiting
  let hasTransitions = not (Array.null allEntering && Array.null allUpdating && Array.null allExiting)
  pure
    { selections: result.selections
    , transitions: if hasTransitions
        then Just $ HATSTransitions
          { entering: allEntering
          , updating: allUpdating
          , exiting: allExiting
          }
        else Nothing
    }
  where
  emptyResult :: InterpResult
  emptyResult = { selections: Map.empty, entering: [], updating: [], exiting: [] }

  -- Process children tracking cumulative DOM position (not logical index)
  -- Returns { result, elementsCreated } to track how many DOM elements were made
  processChildren :: Element -> Array Tree -> Effect InterpResult
  processChildren p children = do
    { result } <- Array.foldM processChild { result: emptyResult, domIdx: 0 } children
    pure result
    where
    processChild :: { result :: InterpResult, domIdx :: Int } -> Tree -> Effect { result :: InterpResult, domIdx :: Int }
    processChild { result: acc, domIdx } child = do
      { result, elementsCreated } <- goWithDomIdx p domIdx child
      pure { result: combineResults acc result, domIdx: domIdx + elementsCreated }

  -- Track DOM position to find existing elements correctly
  goWithDomIdx :: Element -> Int -> Tree -> Effect ProcessResult
  goWithDomIdx p domIdx = case _ of
    Empty -> pure { result: emptyResult, elementsCreated: 0 }

    Elem spec -> do
      existingChildren <- getChildElements p
      el <- case Array.index existingChildren domIdx of
        Just existing -> do
          applyAttrs existing spec.attrs
          applyBehaviors existing spec.behaviors
          pure existing
        Nothing -> do
          el <- createElementWithNS spec.elemType doc
          appendTo p el
          applyAttrs el spec.attrs
          applyBehaviors el spec.behaviors
          pure el
      childResult <- processChildren el spec.children
      pure { result: childResult, elementsCreated: 1 }

    MkFold someFold -> runSomeFold someFold \spec -> do
      -- Process Fold inline to avoid skolem escape from captured variables
      let items = runEnumeration spec.enumerate
      let newKeys = Set.fromFoldable (map spec.keyFn items)

      let tagName = elementTypeToTagName spec.elementType
      existingEls <- getChildElementsForFold p tagName spec.name
      existingKeysAndEls <- traverse (\el -> do
        k <- getKey el
        pure { key: k, element: el }
      ) existingEls

      let existingKeys = Set.fromFoldable (map _.key existingKeysAndEls)
      let enterKeys = Set.difference newKeys existingKeys
      let updateKeys = Set.intersection newKeys existingKeys
      let exitKeys = Set.difference existingKeys newKeys

      -- Process EXIT
      exitTransitions <- traverseWithIndex (\exitIdx { key, element } ->
        if Set.member key exitKeys
          then case spec.gup of
            Just gupSpec -> case gupSpec.exit of
              Just phaseSpec -> do
                -- Create transitions FIRST (reads current values as "from")
                transitions <- createExitTransitions element phaseSpec exitIdx
                -- Apply only non-numeric attrs (colors etc. - can't animate anyway)
                applyNonNumericAttrs element phaseSpec.attrs
                pure $ Just { element, attrs: transitions }
              Nothing -> do
                removeElement element
                pure Nothing
            Nothing -> do
              removeElement element
              pure Nothing
          else pure Nothing
      ) existingKeysAndEls

      -- Process UPDATE
      updateTransitions <- traverseWithIndex (\updateIdx { key, element } ->
        if Set.member key updateKeys
          then case Array.find (\d -> spec.keyFn d == key) items of
            Just datum -> do
              -- Bind updated datum for behaviors that read __data__
              bindDatum element datum
              -- Get the template tree for this datum (captures datum in closures)
              let templateTree = spec.template datum
              let templateAttrs = case templateTree of
                    Elem elemSpec -> elemSpec.attrs
                    _ -> []
              let templateChildren = case templateTree of
                    Elem elemSpec -> elemSpec.children
                    _ -> []
              case spec.gup of
                Just gupSpec -> case gupSpec.update of
                  Just phaseSpec -> do
                    applyNonNumericAttrs element templateAttrs
                    transitions <- createUpdateTransitions element templateAttrs phaseSpec updateIdx
                    -- Clear and rebuild children for UPDATE
                    clearChildren element
                    _ <- traverse (goWithDatum element) templateChildren
                    pure $ Just { element, attrs: transitions }
                  Nothing -> do
                    applyAttrs element templateAttrs
                    -- Clear and rebuild children for UPDATE
                    clearChildren element
                    _ <- traverse (goWithDatum element) templateChildren
                    pure Nothing
                Nothing -> do
                  applyAttrs element templateAttrs
                  -- Clear and rebuild children for UPDATE
                  clearChildren element
                  _ <- traverse (goWithDatum element) templateChildren
                  pure Nothing
            Nothing -> pure Nothing
          else pure Nothing
      ) existingKeysAndEls

      -- Process ENTER
      let enterItems = Array.filter (\d -> Set.member (spec.keyFn d) enterKeys) items
      enterResults <- traverseWithIndex (renderEnteringItem p spec.name spec.keyFn spec.template spec.gup) enterItems

      let updateElements = map _.element (Array.filter (\{ key } -> Set.member key updateKeys) existingKeysAndEls)
      let enterElements = map _.element enterResults
      let childMaps = Array.foldl Map.union Map.empty (map _.childSelections enterResults)
      let selections = Map.insert spec.name (updateElements <> enterElements) childMaps

      -- Count total elements: updated + entered (exited are removed)
      let totalElements = Array.length updateElements + Array.length enterElements

      pure
        { result:
          { selections
          , entering: [Array.catMaybes (map _.transitions enterResults)]
          , updating: [Array.catMaybes updateTransitions]
          , exiting: [Array.catMaybes exitTransitions]
          }
        , elementsCreated: totalElements
        }

  combineResults :: InterpResult -> InterpResult -> InterpResult
  combineResults a b =
    { selections: Map.union a.selections b.selections
    , entering: a.entering <> b.entering
    , updating: a.updating <> b.updating
    , exiting: a.exiting <> b.exiting
    }

  -- Render an entering item
  renderEnteringItem
    :: forall a
     . Element
    -> String
    -> (a -> String)
    -> (a -> Tree)
    -> Maybe (GUPSpec a)
    -> Int
    -> a
    -> Effect { element :: Element, childSelections :: SelectionMap, transitions :: Maybe ElementTransitions }
  renderEnteringItem p foldName keyFn template gupSpec idx datum = do
    let itemTree = template datum  -- Template captures datum in closures
    let key = keyFn datum
    case itemTree of
      Elem spec -> do
        el <- createElementWithNS spec.elemType doc
        appendTo p el
        setKey el key
        setFoldName el foldName
        bindDatum el datum  -- Bind datum for behaviors that read __data__
        applyAttrs el spec.attrs

        transitions <- case gupSpec of
          Just gs -> case gs.enter of
            Just phaseSpec -> do
              ts <- createEnterTransitions el spec.attrs phaseSpec idx
              applyAttrs el phaseSpec.attrs  -- Apply enter phase (starting state)
              pure $ Just { element: el, attrs: ts }
            Nothing -> pure Nothing
          Nothing -> pure Nothing

        applyBehaviors el spec.behaviors
        childMaps <- traverse (goWithDatum el) spec.children
        pure
          { element: el
          , childSelections: Array.foldl Map.union Map.empty (map _.selections childMaps)
          , transitions
          }

      _ -> do
        el <- createElementWithNS Group doc
        pure { element: el, childSelections: Map.empty, transitions: Nothing }

  -- Process child tree (datum already captured in closures)
  goWithDatum :: Element -> Tree -> Effect InterpResult
  goWithDatum p = case _ of
    Empty -> pure emptyResult
    Elem spec -> do
      el <- createElementWithNS spec.elemType doc
      appendTo p el
      applyAttrs el spec.attrs
      applyBehaviors el spec.behaviors
      childResults <- traverse (goWithDatum el) spec.children
      pure $ Array.foldl combineResults emptyResult childResults
    MkFold someFold -> runSomeFold someFold \foldSpec -> do
      let items = runEnumeration foldSpec.enumerate
      results <- traverseWithIndex (renderEnteringItem p foldSpec.name foldSpec.keyFn foldSpec.template foldSpec.gup) items
      let elements = map _.element results
      let childMaps = Array.foldl Map.union Map.empty (map _.childSelections results)
      pure
        { selections: Map.insert foldSpec.name elements childMaps
        , entering: [Array.catMaybes (map _.transitions results)]
        , updating: []
        , exiting: []
        }

  -- ==========================================================================
  -- Attribute Application (Thunked)
  -- ==========================================================================

  applyAttrs :: Element -> Array Attr -> Effect Unit
  applyAttrs el attrs = do
    _ <- traverse (applyAttr el) attrs
    pure unit

  applyAttr :: Element -> Attr -> Effect Unit
  applyAttr el = case _ of
    StaticAttr name value -> setAttribute el name value
    ThunkedAttr name thunk -> setAttribute el name (thunk unit)

  applyNonNumericAttrs :: Element -> Array Attr -> Effect Unit
  applyNonNumericAttrs el attrs = do
    _ <- traverse (applyIfNonNumeric el) attrs
    pure unit

  applyIfNonNumeric :: Element -> Attr -> Effect Unit
  applyIfNonNumeric el = case _ of
    StaticAttr name value ->
      case parseNumber value of
        Just _ -> pure unit  -- Numeric, skip
        Nothing -> setAttribute el name value
    ThunkedAttr name thunk ->
      let value = thunk unit
      in case parseNumber value of
        Just _ -> pure unit
        Nothing -> setAttribute el name value

  -- ==========================================================================
  -- Behavior Application (Thunked)
  -- ==========================================================================

  applyBehaviors :: Element -> Array ThunkedBehavior -> Effect Unit
  applyBehaviors el behaviors = do
    _ <- traverse (applyBehavior el) behaviors
    pure unit

  applyBehavior :: Element -> ThunkedBehavior -> Effect Unit
  applyBehavior el = case _ of
    ThunkedMouseEnter handler -> attachMouseEnterThunked el handler
    ThunkedMouseLeave handler -> attachMouseLeaveThunked el handler
    ThunkedClick handler -> attachClickThunked el handler
    ThunkedDrag SimpleDrag -> attachSimpleDrag el
    ThunkedDrag (SimulationDrag simId) -> attachSimulationDragById el simId
    ThunkedDrag (SimulationDragNested simId) -> attachSimulationDragNestedById el simId
    ThunkedZoom (ZoomConfig cfg) ->
      let ScaleExtent minScale maxScale = cfg.scaleExtent
      in attachZoom el minScale maxScale cfg.targetSelector
    ThunkedCoordinatedHighlight config ->
      let
        -- Wrap classify to convert HighlightClass to Int for FFI
        classifyAsInt :: String -> Int
        classifyAsInt hoveredId = highlightClassToInt (config.classify hoveredId)

        -- Convert TooltipTrigger to Int for FFI
        triggerAsInt = tooltipTriggerToInt config.tooltipTrigger
      in attachCoordinatedHighlightThunked el config.identify classifyAsInt (toNullable config.group) (toNullable config.tooltipContent) triggerAsInt
    ThunkedCoordinatedInteraction config ->
      let
        -- Separate respond functions for each trigger type
        -- JS calls these with raw data, PureScript constructs the ADT
        respondToHover :: String -> Int
        respondToHover hoveredId = interactionStateToInt (config.respond (HoverTrigger hoveredId))

        respondToBrush :: BoundingBox -> Int
        respondToBrush box = interactionStateToInt (config.respond (BrushTrigger box))

        respondToClear :: Unit -> Int
        respondToClear _ = interactionStateToInt (config.respond ClearTrigger)
      in attachCoordinatedInteractionThunked el config.identify respondToHover respondToBrush respondToClear config.position (toNullable config.group)
    ThunkedBrush config ->
      void $ attachCoordinatedBrushThunked el config.extent (toNullable config.group)

  -- ==========================================================================
  -- Transition Creation
  -- ==========================================================================

  createEnterTransitions
    :: Element
    -> Array Attr    -- template attrs (to)
    -> PhaseSpec _   -- enter phase (from)
    -> Int
    -> Effect (Array AttrTransition)
  createEnterTransitions el templateAttrs phaseSpec idx = do
    case phaseSpec.transition of
      Nothing -> pure []
      Just cfg -> do
        let duration = unwrap cfg.duration
        let baseDelay = fromMaybe 0.0 (unwrap <$> cfg.delay)
        let staggerDelay = fromMaybe 0.0 cfg.staggerDelay
        let delay = baseDelay + (staggerDelay * toNumber idx)
        let easing = toTickEasing cfg.easing
        Array.catMaybes <$> traverse (mkEnterTransition duration delay easing templateAttrs) phaseSpec.attrs

  mkEnterTransition
    :: Number -> Number -> _ -> Array Attr -> Attr -> Effect (Maybe AttrTransition)
  mkEnterTransition duration delay easing templateAttrs = case _ of
    StaticAttr name fromVal -> do
      let toVal = findAttrValue name templateAttrs
      case { from: parseNumber fromVal, to: toVal } of
        { from: Just fromNum, to: Just toNum } ->
          pure $ Just { attrName: name, from: fromNum, to: toNum, elapsed: 0.0, duration, delay, easing }
        _ -> pure Nothing
    ThunkedAttr name thunk -> do
      let fromNum = parseNumber (thunk unit)
      let toVal = findAttrValue name templateAttrs
      case { from: fromNum, to: toVal } of
        { from: Just f, to: Just t } ->
          pure $ Just { attrName: name, from: f, to: t, elapsed: 0.0, duration, delay, easing }
        _ -> pure Nothing

  createUpdateTransitions
    :: Element
    -> Array Attr    -- template attrs (to)
    -> PhaseSpec _
    -> Int
    -> Effect (Array AttrTransition)
  createUpdateTransitions el templateAttrs phaseSpec idx = do
    case phaseSpec.transition of
      Nothing -> pure []
      Just cfg -> do
        let duration = unwrap cfg.duration
        let baseDelay = fromMaybe 0.0 (unwrap <$> cfg.delay)
        let staggerDelay = fromMaybe 0.0 cfg.staggerDelay
        let delay = baseDelay + (staggerDelay * toNumber idx)
        let easing = toTickEasing cfg.easing
        Array.catMaybes <$> traverse (mkUpdateTransition el duration delay easing) templateAttrs

  mkUpdateTransition
    :: Element -> Number -> Number -> _ -> Attr -> Effect (Maybe AttrTransition)
  mkUpdateTransition el duration delay easing = case _ of
    StaticAttr name toVal -> do
      fromStr <- getAttribute el name
      case { from: parseNumber fromStr, to: parseNumber toVal } of
        { from: Just fromNum, to: Just toNum } | fromNum /= toNum ->
          pure $ Just { attrName: name, from: fromNum, to: toNum, elapsed: 0.0, duration, delay, easing }
        _ -> pure Nothing
    ThunkedAttr name thunk -> do
      fromStr <- getAttribute el name
      let toNum = parseNumber (thunk unit)
      case { from: parseNumber fromStr, to: toNum } of
        { from: Just f, to: Just t } | f /= t ->
          pure $ Just { attrName: name, from: f, to: t, elapsed: 0.0, duration, delay, easing }
        _ -> pure Nothing

  createExitTransitions
    :: Element
    -> PhaseSpec _
    -> Int
    -> Effect (Array AttrTransition)
  createExitTransitions el phaseSpec idx = do
    case phaseSpec.transition of
      Nothing -> pure []
      Just cfg -> do
        let duration = unwrap cfg.duration
        let baseDelay = fromMaybe 0.0 (unwrap <$> cfg.delay)
        let staggerDelay = fromMaybe 0.0 cfg.staggerDelay
        let delay = baseDelay + (staggerDelay * toNumber idx)
        let easing = toTickEasing cfg.easing
        Array.catMaybes <$> traverse (mkExitTransition el duration delay easing) phaseSpec.attrs

  mkExitTransition
    :: Element -> Number -> Number -> _ -> Attr -> Effect (Maybe AttrTransition)
  mkExitTransition el duration delay easing = case _ of
    StaticAttr name toVal -> do
      fromStr <- getAttribute el name
      case { from: parseNumber fromStr, to: parseNumber toVal } of
        { from: Just fromNum, to: Just toNum } ->
          pure $ Just { attrName: name, from: fromNum, to: toNum, elapsed: 0.0, duration, delay, easing }
        _ -> pure Nothing
    ThunkedAttr name thunk -> do
      fromStr <- getAttribute el name
      let toVal = thunk unit
      case { from: parseNumber fromStr, to: parseNumber toVal } of
        { from: Just fromNum, to: Just toNum } ->
          pure $ Just { attrName: name, from: fromNum, to: toNum, elapsed: 0.0, duration, delay, easing }
        _ -> pure Nothing

  -- ==========================================================================
  -- Helpers
  -- ==========================================================================

  findAttrValue :: String -> Array Attr -> Maybe Number
  findAttrValue name attrs =
    Array.findMap (getAttrNum name) attrs

  getAttrNum :: String -> Attr -> Maybe Number
  getAttrNum targetName = case _ of
    StaticAttr name val | name == targetName -> parseNumber val
    ThunkedAttr name thunk | name == targetName -> parseNumber (thunk unit)
    _ -> Nothing

  parseNumber :: String -> Maybe Number
  parseNumber = Number.fromString

-- ============================================================================
-- Enumeration
-- ============================================================================

runEnumeration :: forall a. Enumeration a -> Array a
runEnumeration = case _ of
  FromArray arr -> arr
  FromTree spec ->
    case spec.order of
      DepthFirst -> enumerateDFS spec.root spec.children spec.includeInternal
      BreadthFirst -> enumerateBFS spec.root spec.children spec.includeInternal
  WithContext items -> map _.datum items

enumerateDFS :: forall a. a -> (a -> Array a) -> Boolean -> Array a
enumerateDFS root getChildren includeInternal = go root
  where
  go node =
    let children = getChildren node
        childResults = Array.concatMap go children
        isLeaf = Array.null children
    in if isLeaf || includeInternal
       then [node] <> childResults
       else childResults

enumerateBFS :: forall a. a -> (a -> Array a) -> Boolean -> Array a
enumerateBFS root getChildren includeInternal = go [root]
  where
  go queue = case Array.uncons queue of
    Nothing -> []
    Just { head: node, tail: rest } ->
      let children = getChildren node
          isLeaf = Array.null children
          include = isLeaf || includeInternal
          thisNode = if include then [node] else []
      in thisNode <> go (rest <> children)

-- ============================================================================
-- FFI
-- ============================================================================

appendTo :: Element -> Element -> Effect Unit
appendTo p child = do
  _ <- Node.appendChild (Element.toNode child) (Element.toNode p)
  pure unit

-- | Remove all children from an element (for UPDATE reconciliation)
clearChildren :: Element -> Effect Unit
clearChildren el = do
  children <- getChildElements el
  traverse_ removeElement children

foreign import selectElement :: String -> Document -> Effect Element
foreign import setAttribute :: Element -> String -> String -> Effect Unit
foreign import getAttribute :: Element -> String -> Effect String
foreign import setKey :: Element -> String -> Effect Unit
foreign import getKey :: Element -> Effect String
foreign import setFoldName :: Element -> String -> Effect Unit
foreign import getChildElements :: Element -> Effect (Array Element)
foreign import getChildElementsForFold :: Element -> String -> String -> Effect (Array Element)
foreign import removeElement :: Element -> Effect Unit
foreign import bindDatum :: forall a. Element -> a -> Effect Unit

-- | Convert ElementType to tag name (lowercase)
elementTypeToTagName :: ElementType -> String
elementTypeToTagName = case _ of
  Circle -> "circle"
  Rect -> "rect"
  Path -> "path"
  Line -> "line"
  Polygon -> "polygon"
  Text -> "text"
  Group -> "g"
  SVG -> "svg"
  Defs -> "defs"
  LinearGradient -> "linearGradient"
  Stop -> "stop"
  PatternFill -> "pattern"
  Div -> "div"
  Span -> "span"
  Table -> "table"
  Tr -> "tr"
  Td -> "td"
  Th -> "th"
  Tbody -> "tbody"
  Thead -> "thead"

-- Thunked behavior FFI - handlers are invoked without datum
foreign import attachMouseEnterThunked :: Element -> (Unit -> Effect Unit) -> Effect Unit
foreign import attachMouseLeaveThunked :: Element -> (Unit -> Effect Unit) -> Effect Unit
foreign import attachClickThunked :: Element -> (Unit -> Effect Unit) -> Effect Unit
foreign import attachZoom :: Element -> Number -> Number -> String -> Effect Unit
foreign import attachSimpleDrag :: Element -> Effect Unit
foreign import attachSimulationDragById :: Element -> String -> Effect Unit
foreign import attachSimulationDragNestedById :: Element -> String -> Effect Unit
foreign import attachCoordinatedHighlightThunked
  :: Element
  -> (Unit -> String)       -- identifyThunk
  -> (String -> Int)        -- classifyFn (returns HighlightClass as Int)
  -> Nullable String        -- groupName
  -> Nullable (Unit -> String)  -- tooltipContentThunk (optional)
  -> Int                    -- tooltipTrigger (OnHover=0, WhenPrimary=1, WhenRelated=2)
  -> Effect Unit

foreign import attachCoordinatedInteractionThunked
  :: Element
  -> (Unit -> String)                                   -- identifyThunk
  -> (String -> Int)                                    -- respondToHover (hoveredId -> state)
  -> (BoundingBox -> Int)                               -- respondToBrush (box -> state)
  -> (Unit -> Int)                                      -- respondToClear (_ -> state)
  -> Maybe (Unit -> { x :: Number, y :: Number })       -- positionThunk (optional)
  -> Nullable String                                    -- groupName
  -> Effect Unit

foreign import attachCoordinatedBrushThunked
  :: Element
  -> BoundingBox                                        -- extent
  -> Nullable String                                    -- groupName
  -> Effect Unit

-- | Convert HighlightClass to Int for FFI
-- | Must match the constants in InterpreterTick.js
highlightClassToInt :: HighlightClass -> Int
highlightClassToInt = case _ of
  HC.Primary -> 0
  HC.Related -> 1
  HC.Dimmed -> 2
  HC.Neutral -> 3
  HC.Upstream -> 4
  HC.Downstream -> 5

-- | Convert TooltipTrigger to Int for FFI
-- | Must match TT_* constants in InterpreterTick.js
tooltipTriggerToInt :: TooltipTrigger -> Int
tooltipTriggerToInt = case _ of
  OnHover -> 0
  WhenPrimary -> 1
  WhenRelated -> 2

-- | Convert InteractionState to Int for FFI (matches Coordinated.stateToInt)
interactionStateToInt :: InteractionState -> Int
interactionStateToInt = case _ of
  IS.Primary -> 0
  IS.Related -> 1
  IS.Selected -> 2
  IS.Dimmed -> 3
  IS.Neutral -> 4
