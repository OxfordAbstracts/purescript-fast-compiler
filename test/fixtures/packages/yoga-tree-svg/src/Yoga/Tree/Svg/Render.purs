module Yoga.Tree.Svg.Render
    ( Slots, NodeSlot, _item, _preview
    , GraphStatus(..), NodeMode(..), EdgeMode(..), NodeStatus(..), SoftLimit(..)
    , NodeQuery, NodeOutput
    , GraphConfig, Modes, RenderConfig, Events, Geometry, ValueConfig
    , NodeComponent, NodeComponentInput, GraphHtml
    , renderGraph, renderGraph_, renderGraph'
    , renderGraphFrom, renderGraphFrom_, renderGraphFrom'
    , renderPreview, renderPreview_, renderPreview'
    , WithStatus, statusColor
    , toValueConfig
    )
    where

import Prelude

import Type.Proxy (Proxy(..))

import Prim.Row (class Cons) as Row

import Data.Symbol (class IsSymbol)
import Data.Number (pi) as Number
import Data.Map (Map)
import Data.Int (toNumber) as Int
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Graph (Graph, Edge)
import Data.Graph (toMap, fromMap, lookup) as Graph
import Data.Map (empty, lookup, insert, update, filterKeys, delete) as Map
import Data.Array (fromFoldable, toUnfoldable, length, reverse, filter, take, drop) as Array
import Data.Tuple (fst, snd, uncurry) as Tuple
import Data.List (List(..))
import Data.List (length, reverse, filter, take, drop) as List
import Data.Foldable (class Foldable, foldl, foldr)
import Data.FunctorWithIndex (mapWithIndex)
import Data.Tuple.Nested ((/\), type (/\))
import Data.Bifunctor (lmap)

import Yoga.Tree.Extended.Path (Path(..))
import Yoga.Tree.Extended.Path (root, up, lastPos, depth, startsWith) as Path

import Yoga.Tree.Svg.Geometry (Position, Positioned, Size, findPosition, scale, rotateBy)
import Yoga.Tree.Svg.Style as Style
import Yoga.Tree.Svg.Style (Theme(..))

import Halogen as H
import Halogen.HTML (HTML)
import Halogen.HTML as HH
import Halogen.HTML.Properties as HHP
import Halogen.HTML.Events as HE
import Halogen.Svg.Attributes as HSA
import Halogen.Svg.Elements as HS


type NodeSlot = H.Slot NodeQuery NodeOutput Path


type Slots =
  ( item    :: NodeSlot
  , preview :: NodeSlot
  , pinned  :: NodeSlot
  )


_item  = Proxy :: _ "item"
_preview  = Proxy :: _ "preview"
_pinned  = Proxy :: _ "pinned"


data NodeQuery x = NodeQuery
type NodeOutput = Void


data NodeMode
    = Text
    | JustNode
    | NodeWithLabel
    | Component


data EdgeMode
    = JustEdge
    | EdgeWithLabel


data GraphStatus
    = GKeysFocus
    | GHoverFocus
    | GGhostFocus
    | GNormal


data NodeStatus
    = Normal
    | FocusRoot -- when the node is in the root of current navigation
    | KeysFocus -- when user focused over the node with keys
    | KeysNext -- when node is the candidate for being selected next
    | HoverFocus -- when node is hovered with mouse cursor (preview)
    | HoverGhost -- when cursor left the node but no other node was hovered over (ghost preview)
    | Selected -- when node is the part of current selection
    | Pinned -- when node is pinned
    | Combo NodeStatus NodeStatus


data SoftLimit
    = Infinite
    | Maximum Int


data ChLimit
    = AtStart Int
    | Between Int Int
    | AtEnd Int Int


data Visibility a
    = AllVisible a
    | DepthLimitReached a
    | ChildrenLimitReached ChLimit a
    -- | ChildrenBefore Int a
    -- | ChidlrenAfter Int a


derive instance Eq NodeStatus


foldl' :: forall f a b. Foldable f => (b -> a -> b) -> f a -> b -> b
foldl' = flip <<< foldl


type PositionedMap a = Map Path (Positioned a)
type GraphMap a = Map Path (a /\ Array Path)
type PositionedGraphMap a = GraphMap (Positioned a)
type PathDupGraphMap a = Map Path (Path /\ a /\ Array Path)
type PathDupMapItem a = (Path /\ a /\ Array Path)


distributePositions :: forall a. From -> Geometry -> (Path -> a -> Size) -> Graph Path a -> PositionedGraphMap (Visibility a)
distributePositions { root, current } geom getSize graph =
    filledGraphMap
        # foldl (flip distribute) Map.empty
        # fillBackChildren
        <#> (lmap
                $ scale
                $ min geom.scaleLimit.max
                $ max geom.scaleLimit.min geom.scaleFactor
            )

    where
        graphMap = Graph.toMap graph <#> map Array.fromFoldable :: GraphMap a
        filledGraphMap =
            graphMap
                # addPathsToValues
                # reduceVisibilityIfNeeded
            :: PathDupGraphMap (Visibility a)
        zeroPos = { x : 0.0, y : 0.0 }
        childPos parentPos =
            findPosition geom.baseDistance parentPos 0.0 (2.0 * Number.pi / 3.0)
        injectRect value pos size =
            { x : pos.x, y : pos.y, width : size.width, height : size.height, value }
        calcTheta rotData =
            let
                angleStart = -1.0 * (total / 2.0)
                angleEnd   =  1.0 * (total / 2.0)
                total = neighNum * (Number.pi / 10.0)
                neighNum = Int.toNumber rotData.neighbours
                posNum = Int.toNumber rotData.pos
            in -1.0 * (angleStart + (posNum / (neighNum - 1.0)) * total)

        addPathsToValues :: GraphMap a -> PathDupGraphMap a
        addPathsToValues = mapWithIndex ((/\))

        reduceVisibilityIfNeeded :: PathDupGraphMap a -> PathDupGraphMap (Visibility a)
        reduceVisibilityIfNeeded = case geom.depthLimit /\ geom.childrenLimit of
            Infinite /\ Infinite -> map $ map $ lmap AllVisible
            Infinite /\ Maximum chLimit -> applyChidrenLimit chLimit identity
            Maximum dLimit /\ Infinite -> applyDepthLimit dLimit identity
            Maximum dLimit /\ Maximum chLimit -> applyChidrenLimit chLimit joinVis <<< applyDepthLimit dLimit identity

        inParent :: Path -> { neighbours :: Int, pos :: Int }
        inParent path =
            { neighbours : Map.lookup (Path.up path) graphMap <#> Tuple.snd <#> Array.length # fromMaybe 0
            , pos : Path.lastPos path # fromMaybe (-1)
            }

        fillBackChildren :: PositionedMap (Visibility a) -> PositionedGraphMap (Visibility a)
        fillBackChildren = mapWithIndex \path cell -> cell /\ (Map.lookup path graphMap <#> Tuple.snd # fromMaybe [])

        distribute :: PathDupMapItem (Visibility a) -> PositionedMap (Visibility a) -> PositionedMap (Visibility a)
        distribute (curPath /\ curValue /\ childPaths) prevPositions =
            case prevPositions # Map.lookup curPath of
                Nothing -> -- we didn't visit `curPath` as a child of some other node: it's probably a root node
                    prevPositions
                            # storeRect curPath curValue zeroPos (getSize curPath $ fromVis curValue)
                            # positionChildrenFrom zeroPos childPaths -- for now, position children from zero position
                Just { x, y } -> -- we did located `curPath` as a child of some other node before, we can position its chidren relatively
                    let
                        rotData = inParent curPath
                    in prevPositions
                        # positionChildrenFrom { x, y } childPaths
                        # rotateAll { x, y } (calcTheta rotData) childPaths

        storeRect :: Path -> Visibility a -> Position -> Size -> PositionedMap (Visibility a) -> PositionedMap (Visibility a)
        storeRect path value position size =
            Map.insert path $ injectRect value position size

        positionChildrenFrom :: Position -> Array Path -> PositionedMap (Visibility a) -> PositionedMap (Visibility a)
        positionChildrenFrom parentPos childPaths =
            foldl' (flip $ insertChildPos parentPos $ Array.length childPaths) $ mapWithIndex (/\) (Array.reverse childPaths)

        rotateAll :: Position -> Number -> Array Path -> PositionedMap (Visibility a) -> PositionedMap (Visibility a)
        rotateAll parentPos theta childPaths =
            foldl'
                (\positions chPath ->
                    Map.update
                        (\rec ->
                            let
                                rotated = rotateBy parentPos { x : rec.x, y : rec.y  } 1.0 theta
                            in Just $ rec { x = rotated.x, y = rotated.y }
                        )
                        chPath
                        positions)
                childPaths

        insertChildPos :: Position -> Int -> Int /\ Path -> PositionedMap (Visibility a) -> PositionedMap (Visibility a)
        insertChildPos parentPos childrenCount (index /\ childPath) prevPositions =
            -- case graphMap # Map.lookup childPath <#> Tuple.fst of -- FIXME: maybe there is a faster way to extract value?
            -- case prevPositions # Map.lookup (unsafeConcat root childPath) <#> _.value of
            case filledGraphMap # Map.lookup childPath <#> Tuple.snd <#> Tuple.fst of -- FIXME: maybe there is a faster way to access the value?
                Just visChildValue ->
                    prevPositions
                        # storeRect childPath visChildValue (childPos parentPos childrenCount index) (getSize childPath $ fromVis visChildValue)
                Nothing ->
                    prevPositions

        applyDepthLimit :: forall x y. Int -> (Visibility x -> y) -> PathDupGraphMap x -> PathDupGraphMap y
        applyDepthLimit dLimit f = map processVal <<< Map.filterKeys notTooDeep
            where
                notTooDeep path = (Path.depth path - Path.depth root) <= dLimit
                checkVDepth :: Int -> x -> Path -> Visibility x
                checkVDepth chCount x path | chCount > 0 && (Path.depth path - Path.depth root) == dLimit = DepthLimitReached x
                checkVDepth _       x _    | otherwise = AllVisible x
                processVal :: PathDupMapItem x -> Path /\ y /\ Array Path
                processVal (path /\ x /\ xs) = path /\ (f $ checkVDepth (Array.length xs) x path) /\ Array.filter notTooDeep xs

        applyChidrenLimit :: forall x y. Int -> (Visibility x -> y) -> PathDupGraphMap x -> PathDupGraphMap y
        applyChidrenLimit chLimit f = map checkChCount >>> foldl foldF ([] /\ Map.empty) >>> Tuple.uncurry (flip removeAllDropped)
            where
                -- FIXME: first, collect all paths for the chidren of ... of the "dropped" chidlren, then filter out path duplicates using a `Set`,
                --        and only then remove all entries from the `Map`: it should be much faster than the current method
                removeAllDropped :: PathDupGraphMap y -> Array Path -> PathDupGraphMap y
                removeAllDropped = foldr removeOneDropped
                removeOneDropped :: Path -> PathDupGraphMap y -> PathDupGraphMap y
                removeOneDropped path theMap =
                    case Map.lookup path theMap of
                        Just (_ /\ _ /\ xs) -> xs # foldr removeOneDropped theMap # Map.delete path
                        Nothing -> theMap # Map.delete path
                foldF :: (Array Path /\ PathDupGraphMap y) -> Path /\ y /\ { dropped :: Array Path, left :: Array Path } -> (Array Path /\ PathDupGraphMap y)
                foldF (prevDropped /\ collectMap) (p /\ y /\ { dropped, left }) = (prevDropped <> dropped) /\ (Map.insert p (p /\ y /\ left) collectMap)
                checkChCount :: PathDupMapItem x -> Path /\ y /\ { dropped :: Array Path, left :: Array Path }
                checkChCount (path /\ x /\ xs) | (Array.length xs > chLimit) =
                    if (Path.startsWith current path) && (Path.depth current == (Path.depth path + 1)) then
                        let
                            childrenCount = Array.length xs
                            mbSelectionIdx = Path.lastPos current
                            firstSplit  = maybe 0 (\selIdx -> max 0             $ selIdx + 1 - chLimit) mbSelectionIdx
                            secondSplit = min childrenCount $ firstSplit + chLimit
                            prefix = Array.take firstSplit xs
                            withSelection = Array.take (secondSplit - firstSplit) $ Array.drop firstSplit xs
                            suffix = Array.drop secondSplit xs
                            limitValue = if firstSplit == 0
                                            then AtStart secondSplit
                                            else if secondSplit == childrenCount
                                                then AtEnd firstSplit secondSplit
                                                else Between firstSplit secondSplit
                        in
                        path /\ (f $ ChildrenLimitReached limitValue x) /\ { left : withSelection, dropped : prefix <> suffix }
                    else
                        path /\ (f $ ChildrenLimitReached (AtStart chLimit) x) /\ { left : Array.take chLimit xs, dropped : Array.drop chLimit xs }
                checkChCount (path /\ x /\ xs) | otherwise
                      = path /\ (f $ AllVisible x) /\ { dropped : [], left : xs }


distributePositions' :: forall a. From -> Geometry -> (Path -> a -> Size) -> Graph Path a -> Graph Path (Positioned (Visibility a))
distributePositions' from geom getSize graph =
    distributePositions from geom getSize graph <#> (map Array.toUnfoldable) # Graph.fromMap


type RenderConfig a =
    { valueLabel :: Path -> a -> String
    , valueColor :: Theme -> Path -> a -> HSA.Color
    , valueLabelColor :: Theme -> Path -> a -> HSA.Color
    , valueLabelWidth :: Path -> a -> Int
    , edgeColor :: Theme -> Path -> a -> Path -> a -> HSA.Color
    , edgeLabel :: Path -> a -> Path -> a -> String
    , componentSize :: Path -> a -> { width :: Number, height :: Number }
    }


type GraphConfig a i =
    { render :: RenderConfig a
    , geometry :: Geometry
    , modes :: Modes
    , events :: Events i a
    , theme :: Theme
    }


type ValueConfig a =
    { render :: RenderConfig a
    , geometry :: Geometry
    , nodeMode :: NodeMode
    , theme :: Theme
    }


type Events i a =
    { valueClick :: Path -> a -> i
    , valueOver  :: Path -> a -> i
    , valueOut   :: Path -> a -> i
    }


type Modes =
    { nodeMode :: NodeMode
    , edgeMode :: EdgeMode
    , previewMode :: NodeMode
    , pinMode :: NodeMode
    -- TODO maximum amount of childNodes
    }


type Geometry =
    { scaleFactor :: Number
    , baseDistance :: Number
    , valueRadius :: Number -- = 5.0 :: Number
    , scaleLimit :: { min :: Number, max :: Number }
    , depthLimit :: SoftLimit
    , childrenLimit :: SoftLimit
    }


type NodeComponent m a
    = H.Component NodeQuery (NodeComponentInput a) NodeOutput m


type NodeComponentInput a =
    { theme :: Theme
    , path :: Path
    , value :: a
    }


type From =
    { root :: Path
    , current :: Path
    }


type GraphHtml m i  = HTML (H.ComponentSlot Slots m i) i


type WithStatus a = NodeStatus /\ a


_statusOf :: forall a. WithStatus a -> NodeStatus
_statusOf = Tuple.fst


_valueOf :: forall a. WithStatus a -> a
_valueOf = Tuple.snd


toValueConfig :: forall a i. GraphConfig a i -> ValueConfig a
toValueConfig { render, modes, geometry, theme } =
    { render, theme, geometry, nodeMode : modes.nodeMode }


renderGraph :: forall a i m. GraphStatus -> GraphConfig a i -> Events i a -> Graph Path (WithStatus a) -> Array (GraphHtml m i)
renderGraph gstatus config = renderGraph' gstatus config Nothing


renderGraph_ :: forall a i m. GraphStatus -> GraphConfig a i -> NodeComponent m a -> Events i a -> Graph Path (WithStatus a) -> Array (GraphHtml m i)
renderGraph_ gstatus config childComp = renderGraph' gstatus config $ Just childComp


renderGraph' :: forall a i m. GraphStatus -> GraphConfig a i -> Maybe (NodeComponent m a) -> Events i a -> Graph Path (WithStatus a) -> Array (GraphHtml m i)
renderGraph' = renderGraphFrom' { root : Path.root, current : Path.root }


renderGraphFrom :: forall a i m. From -> GraphStatus -> GraphConfig a i -> Events i a -> Graph Path (WithStatus a) -> Array (GraphHtml m i)
renderGraphFrom from gstatus config = renderGraphFrom' from gstatus config Nothing


renderGraphFrom_ :: forall a i m. From -> GraphStatus -> GraphConfig a i -> NodeComponent m a -> Events i a -> Graph Path (WithStatus a) -> Array (GraphHtml m i)
renderGraphFrom_ from gstatus config childComp = renderGraphFrom' from gstatus config $ Just childComp


renderGraphFrom' :: forall a i m. From -> GraphStatus -> GraphConfig a i -> Maybe (NodeComponent m a) -> Events i a -> Graph Path (WithStatus a) -> Array (GraphHtml m i)
renderGraphFrom' from gstatus config mbComponent events graph = foldl (<>) [] $ mapWithIndex renderNode positionsMap
    where
        modes   = config.modes :: Modes
        geom    = config.geometry :: Geometry
        rconfig = config.render :: RenderConfig a
        vconfig = toValueConfig config :: ValueConfig a
        statusOf :: Path -> NodeStatus
        statusOf path = Graph.lookup path graph <#> _statusOf # fromMaybe Normal
        valuesGraph :: Graph Path a
        valuesGraph = graph <#> _valueOf
        positionsMap :: PositionedGraphMap (Visibility a)
        positionsMap = distributePositions from geom rconfig.componentSize valuesGraph
        keyLabelOffset = { x : -1.0 * (geom.valueRadius / 2.0), y : -7.0 }
        depthLimitOffset = { x : -1.0 * (geom.valueRadius / 2.0), y : 3.0 * geom.valueRadius }
        chOffsetY = 3.0 -- 0.0
        childLimitOffsetR = { x : 3.0 * (geom.valueRadius / 2.0), y : chOffsetY }
        childLimitOffsetL = { x : -1.0 * (geom.valueRadius / 2.0) - 15.0, y : chOffsetY }

        renderValue :: Path -> Positioned (Visibility a) -> _
        renderValue nodePath { x, y, value } =
            HS.g
                [ HSA.transform $ pure $ HSA.Translate x y
                , HHP.style Style.value
                , HE.onClick     $ const $ events.valueClick nodePath $ fromVis value
                , HE.onMouseOver $ const $ events.valueOver  nodePath $ fromVis value
                , HE.onMouseOut  $ const $ events.valueOut   nodePath $ fromVis value
                ]
                $ [ _renderValue gstatus vconfig _item mbComponent (statusOf nodePath) { x : 0.0, y : 0.0 } nodePath $ fromVis value
                , case (statusOf nodePath) of
                    KeysNext ->
                        textAt keyLabelOffset Style.orA $
                            case Path.lastPos nodePath of -- TODO: pass index of the item instead
                            Just lastVal -> show lastVal
                            Nothing -> "?"
                    _ -> noText
                , case value of
                    AllVisible _ -> noText
                    DepthLimitReached _ ->
                        textAt depthLimitOffset Style.maB "↓"
                    ChildrenLimitReached chLimit _ ->
                        case chLimit of
                            AtStart _ ->
                                textAt childLimitOffsetR Style.maB "->"
                            Between _ _ ->
                                HS.g []
                                    [ textAt childLimitOffsetL Style.maB "<-"
                                    , textAt childLimitOffsetR Style.maB "->"
                                    ]
                            AtEnd _ _ -> textAt childLimitOffsetL Style.maB "<-"
                            -- AtStart n -> "0-" <> show (n - 1) <> "->"
                            -- Between a b -> "<-" <> show a <> "-" <> show (b - 1) <> "->"
                            -- AtEnd a b -> "<-" <> show a <> "-" <> show (b - 1)
                ]
        renderEdge parentPath parent childPath =
            case Map.lookup childPath positionsMap <#> Tuple.fst of
                Just child ->
                    HS.g
                        [ HHP.style Style.edge ]
                        $ pure
                        $ _renderEdge config.theme gstatus { start : statusOf parentPath, end : statusOf childPath } modes.edgeMode rconfig
                        $
                            { start : { path : parentPath, pos : { x : parent.x, y: parent.y }, value : fromVis $ parent.value }
                            , end   : { path : childPath,  pos : { x : child.x,  y: child.y  }, value : fromVis $ child.value  }
                            }
                Nothing -> HS.g [] []

        renderNode :: Path -> (Positioned (Visibility a) /\ Array Path) -> _
        renderNode nodePath (va /\ paths) =
            (renderEdge nodePath va <$> Array.fromFoldable paths)
            <> [ renderValue nodePath va ]

        noText = HS.text [] [ HH.text "" ]
        textAt pos colorF text =
            HS.text
                [ HSA.x pos.x
                , HSA.y pos.y
                , HSA.fill $ colorF config.theme
                ]
                [ HH.text text ]


renderPreview :: forall a i m. ValueConfig a -> NodeStatus -> Path -> a -> GraphHtml m i
renderPreview vconfig = renderPreview' vconfig Nothing


renderPreview_ :: forall a i m. ValueConfig a -> NodeComponent m a -> NodeStatus -> Path -> a -> GraphHtml m i
renderPreview_ vconfig childComp = renderPreview' vconfig (Just childComp)


renderPreview' :: forall a i m. ValueConfig a -> Maybe (NodeComponent m a) -> NodeStatus -> Path -> a -> GraphHtml m i
renderPreview' vconfig mbComponent nodeStatus nodePath value =
    let
        componentSize = vconfig.render.componentSize nodePath value
        padding = 5.0
        position =
            case vconfig.nodeMode of
              Component ->
                { x : 0.0
                , y : componentSize.height / 2.0
                }
              _ ->
                { x : componentSize.width  / 2.0
                , y : componentSize.height / 2.0
                }
    in
        HS.svg
            [ HSA.width  $ componentSize.width + padding * 2.0
            , HSA.height $ componentSize.height + padding * 2.0
            ]
            [ HS.rect
                [ HSA.width  $ componentSize.width + padding * 2.0
                , HSA.height $ componentSize.height + padding * 2.0
                , HSA.stroke $ _strokeFromStatus vconfig.theme nodeStatus
                , HSA.strokeWidth $ _strokeWidthFromStatus nodeStatus
                , HSA.fill $ HSA.RGBA 0 0 0 0.0
                ]
            , HS.g
                [ HHP.style Style.previewBox
                , HSA.transform $ pure $ HSA.Translate padding padding
                ]
                $ pure
                $ _renderValue GNormal vconfig _preview mbComponent nodeStatus position nodePath value
            ]


statusColor :: Theme -> NodeStatus -> HSA.Color
statusColor th = case _ of
  Normal -> HSA.RGBA 0 0 0 0.0
  FocusRoot -> Style.alpha 0.6 $ Style.reA th
  HoverFocus -> Style.alpha 0.6 $ Style.grB th
  HoverGhost -> Style.alpha 0.6 $ Style.grA th
  Selected -> Style.alpha 0.6 $ Style.blB th
  KeysNext -> Style.alpha 0.6 $ Style.blA th
  _ -> HSA.RGBA 0 0 0 0.0


type EdgeJoint a =
    { path :: Path
    , value :: a
    , pos :: Position
    }


type EdgeDef a = Edge (EdgeJoint a)


type EdgeStatus = Edge NodeStatus


_renderEdge :: forall a p i. Theme -> GraphStatus -> EdgeStatus -> EdgeMode -> RenderConfig a -> EdgeDef a -> HTML p i
_renderEdge th gstatus estatus EdgeWithLabel rconfig edge =
    let
        parent = edge.start
        child = edge.end
        parentPos = parent.pos
        childPos= child.pos
    in HS.g []
        [ HS.line
            [ HSA.x1 parentPos.x
            , HSA.y1 parentPos.y
            , HSA.x2 childPos.x
            , HSA.y2 childPos.y
            , HSA.stroke $ rconfig.edgeColor th parent.path parent.value child.path child.value
            ]
        , HS.text
            [ HSA.x $ parentPos.x + ((childPos.x - parentPos.x) / 2.0)
            , HSA.y $ parentPos.y + ((childPos.y - parentPos.y) / 2.0)
            ]
            [ HH.text $ rconfig.edgeLabel parent.path parent.value child.path child.value ]
        ]
_renderEdge th gstatus estatus JustEdge rconfig edge =
    let
        parent = edge.start
        child = edge.end
        parentPos = parent.pos
        childPos= child.pos
    in HS.g []
        [ HS.line
            [ HSA.x1 parentPos.x
            , HSA.y1 parentPos.y
            , HSA.x2 childPos.x
            , HSA.y2 childPos.y
            , HSA.stroke $ rconfig.edgeColor th parent.path parent.value child.path child.value
            , HSA.strokeOpacity $ _edgeOpacity gstatus estatus
            ]
        ]

_renderValue
    :: forall slot r' i m a
     . IsSymbol slot
    => Row.Cons slot NodeSlot r' Slots
    => GraphStatus
    -> ValueConfig a
    -> Proxy slot
    -> Maybe (NodeComponent m a)
    -> NodeStatus
    -> Position
    -> Path
    -> a
    -> GraphHtml m i
_renderValue gstatus vconfig =
    _renderValue' vconfig.theme gstatus vconfig.nodeMode vconfig.geometry vconfig.render



_renderValue'
    :: forall slot r' i m a
     . IsSymbol slot
    => Row.Cons slot NodeSlot r' Slots
    => Theme
    -> GraphStatus
    -> NodeMode
    -> Geometry
    -> RenderConfig a
    -> Proxy slot
    -> Maybe (NodeComponent m a)
    -> NodeStatus
    -> Position
    -> Path
    -> a
    -> GraphHtml m i
_renderValue' th gstatus NodeWithLabel geom rconfig _ _ status pos nodePath value =
    HS.g
        []
        [ HS.circle
            [ HSA.cx pos.x
            , HSA.cy pos.y
            , HSA.r geom.valueRadius
            , HSA.fill          $ rconfig.valueColor th nodePath value
            , HSA.stroke        $ _strokeFromStatus th status
            , HSA.strokeWidth   $ _strokeWidthFromStatus status
            , HSA.fillOpacity   $ _nodeOpacity gstatus status
            , HSA.strokeOpacity $ _nodeOpacity gstatus status
            ]
        , HS.rect
            [ HSA.fill $ Style.blA th
            , HSA.x $ pos.x
            , HSA.y $ pos.y - 2.0
            , HSA.rx 6.0
            , HSA.ry 6.0
            , HSA.width $ Int.toNumber (rconfig.valueLabelWidth nodePath value) * 8.0 + 5.0
            , HSA.height 15.0
            , HSA.fillOpacity $ case status of
                Normal -> 0.1
                FocusRoot -> 0.0
                KeysFocus -> 0.6
                KeysNext -> 0.35
                HoverFocus -> 0.3
                HoverGhost -> 0.2
                Selected -> 0.6
                Pinned -> 0.0
                _ -> 0.1
            ]
        , HS.text
            [ HSA.fill $ rconfig.valueLabelColor th nodePath value
            , HSA.x $ pos.x + 6.0
            , HSA.y $ pos.y + 9.0
            ]
            [ HH.text $ rconfig.valueLabel nodePath value
            ]
        ]
_renderValue' th gstatus JustNode geom rconfig _ _ status pos nodePath value =
    HS.g
        []
        [ HS.circle
            [ HSA.cx pos.x
            , HSA.cy pos.y
            , HSA.r geom.valueRadius
            , HSA.fill          $ rconfig.valueColor th nodePath value
            , HSA.stroke        $ _strokeFromStatus th status
            , HSA.strokeWidth   $ _strokeWidthFromStatus status
            , HSA.fillOpacity   $ _nodeOpacity gstatus status
            , HSA.strokeOpacity $ _nodeOpacity gstatus status
            ]
        ]
_renderValue' th gstatus Component _ _ _ Nothing status pos _ _ =
    HS.text
        [ HSA.x pos.x, HSA.y pos.y
        , HSA.fill $ HSA.RGB 0 0 0
        ]
        [ HH.text "NO COMPONENT" ]
_renderValue' th gstatus Component _ _ pslot (Just childComp) status pos nodePath value =
    HS.g
        [ HSA.transform $ pure $ HSA.Translate pos.x pos.y ]
        $ pure
        $ HH.slot_
            pslot
            nodePath
            childComp
            { theme : th
            , path : nodePath
            , value
            }
_renderValue' th gtatus Text _ rconfig _ _ _ pos nodePath value =
    HS.g
        []
        [ HS.text
            [ HSA.fill $ rconfig.valueLabelColor th nodePath value
            , HSA.x $ pos.x + 6.0
            , HSA.y $ pos.y + 9.0
            ]
            [ HH.text $ rconfig.valueLabel nodePath value
            ]
        ]


_strokeFromStatus :: Theme -> NodeStatus -> HSA.Color
_strokeFromStatus th = case _ of
  Normal -> Style.tx th
  FocusRoot -> Style.reA th
  HoverFocus -> Style.grB th
  HoverGhost -> Style.grA th
  Selected -> Style.blB th
  KeysNext -> Style.blA th
  _ -> HSA.RGB 0 0 0


_strokeWidthFromStatus :: NodeStatus -> Number
_strokeWidthFromStatus  = case _ of
  Normal -> 1.0
  FocusRoot -> 2.0
  HoverFocus -> 3.0
  HoverGhost -> 2.0
  Selected -> 3.0
  KeysNext -> 2.0
  _ -> 1.0


_nodeOpacity :: GraphStatus -> NodeStatus -> Number
_nodeOpacity GNormal _ = 1.0
_nodeOpacity GKeysFocus FocusRoot = 0.6
_nodeOpacity GKeysFocus KeysFocus = 1.0
_nodeOpacity GKeysFocus KeysNext = 1.0
_nodeOpacity GKeysFocus Selected = 1.0
_nodeOpacity GKeysFocus _ = 0.4
_nodeOpacity GHoverFocus FocusRoot = 1.0
_nodeOpacity GHoverFocus KeysFocus = 0.7
_nodeOpacity GHoverFocus KeysNext = 0.7
_nodeOpacity GHoverFocus Selected = 1.0
_nodeOpacity GHoverFocus _ = 0.5
_nodeOpacity GGhostFocus _ = 1.0


_oneOf :: NodeStatus -> EdgeStatus -> Boolean
_oneOf ns { start, end } = ns == start || ns == end

_startOf :: NodeStatus -> EdgeStatus -> Boolean
_startOf ns { start } = ns == start

_endOf :: NodeStatus -> EdgeStatus -> Boolean
_endOf ns { start } = ns == start


_edgeOpacity :: GraphStatus -> EdgeStatus -> Number
_edgeOpacity GNormal _ = 1.0
_edgeOpacity GKeysFocus estatus | _oneOf KeysFocus estatus = 1.0
_edgeOpacity GKeysFocus estatus | _oneOf Selected estatus = 1.0
_edgeOpacity GKeysFocus estatus | _startOf KeysNext estatus = 0.6
_edgeOpacity GKeysFocus estatus | _endOf KeysNext estatus = 1.0
_edgeOpacity GKeysFocus estatus | _oneOf FocusRoot estatus = 0.3
_edgeOpacity GKeysFocus _ = 0.1
_edgeOpacity GHoverFocus estatus | _oneOf HoverFocus estatus = 1.0
_edgeOpacity GHoverFocus estatus | _oneOf HoverGhost estatus = 1.0
_edgeOpacity GHoverFocus estatus | _oneOf Selected estatus = 1.0
_edgeOpacity GHoverFocus estatus | _oneOf FocusRoot estatus = 0.3
_edgeOpacity GHoverFocus estatus | _oneOf KeysFocus estatus = 0.3
_edgeOpacity GHoverFocus estatus | _oneOf KeysNext estatus = 0.3
_edgeOpacity GHoverFocus _ = 0.1
_edgeOpacity GGhostFocus _ = 1.0


fromVis :: forall a. Visibility a -> a
fromVis = case _ of
    AllVisible a -> a
    DepthLimitReached a -> a
    ChildrenLimitReached _ a -> a
    -- ChildrenBefore _ a -> a
    -- ChidlrenAfter _ a -> a


joinVis :: forall a. Visibility (Visibility a) -> Visibility a
joinVis (ChildrenLimitReached n vis) = ChildrenLimitReached n $ fromVis vis
joinVis (DepthLimitReached (AllVisible a)) = DepthLimitReached a
joinVis (DepthLimitReached vis) = DepthLimitReached $ fromVis vis -- vis
joinVis (AllVisible vis) = vis
