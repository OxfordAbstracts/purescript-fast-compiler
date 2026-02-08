module Grain.Virtualized
  ( Props
  , virtualList
  ) where

import Prelude

import Data.Array (concat, snoc)
import Data.Foldable (foldl)
import Data.Maybe (Maybe(..))
import Grain (class LocalGrain, LProxy(..), VNode, fromConstructor, useUpdater, useValue)
import Grain.Markup as H
import Web.DOM.Element as E
import Web.Event.Event (target)

-- | The type of virtual list props.
-- |
-- | - `height`: The px height of container
-- | - `rows`: The data for row view
-- | - `rowView`: The renderer of a row
-- | - `calcRowHeight`: The calculator of a row view's px height
type Props a =
  { height :: Number
  , rows :: Array a
  , rowView :: { style :: String, row :: a } -> VNode
  , calcRowHeight :: a -> Number
  }

type Params =
  { topPadding :: Number
  , bottomPadding :: Number
  , renderingHeight :: Number
  , renderingTargets :: Array VNode
  }

newtype ScrollTop = ScrollTop Number

instance localGrainScrollTop :: LocalGrain ScrollTop where
  initialState _ = pure $ ScrollTop 0.0
  typeRefOf _ = fromConstructor ScrollTop

-- | Render a virtual list.
virtualList :: forall a. Props a -> VNode
virtualList props = H.component do
  ScrollTop scrollTop <- useValue (LProxy :: _ ScrollTop)
  updateScrollTop <- useUpdater (LProxy :: _ ScrollTop)

  let style = "overflow:auto;height:" <> show props.height <> "px;"

      children = calculateChildren props scrollTop

      onScroll evt =
        case join $ E.fromEventTarget <$> target evt of
          Nothing -> pure unit
          Just element -> do
            scrollTop' <- E.scrollTop element
            updateScrollTop $ const $ ScrollTop scrollTop'

  pure $ H.div
    # H.style style
    # H.onScroll onScroll
    # H.kids children

calculateChildren :: forall a. Props a -> Number -> Array VNode
calculateChildren props scrollTop =
  let params = calculateParams props scrollTop
      topPadding = H.key "_virtualized_top_padding" $ padding params.topPadding
      bottomPadding = H.key "_virtualized_bottom_padding" $ padding params.bottomPadding
   in concat [ [ topPadding ], params.renderingTargets, [ bottomPadding ] ]

calculateParams
  :: forall a
   . Props a
  -> Number
  -> Params
calculateParams props scrollTop =
  foldl
    (calculateParamsByRow props scrollTop)
    { topPadding: 0.0
    , bottomPadding: 0.0
    , renderingHeight: 0.0
    , renderingTargets: []
    }
    props.rows

calculateParamsByRow
  :: forall a
   . Props a
  -> Number
  -> Params
  -> a
  -> Params
calculateParamsByRow props scrollTop params row =
  if params.topPadding + rowHeight < scrollTop then
    params { topPadding = params.topPadding + rowHeight }
  else if params.renderingHeight < props.height + rowHeight then
    params
      { renderingHeight = params.renderingHeight + rowHeight
      , renderingTargets =
          snoc params.renderingTargets
            $ calculateRowView props rowHeight row
      }
  else
    params { bottomPadding = params.bottomPadding + rowHeight }
  where
    rowHeight = props.calcRowHeight row

calculateRowView :: forall a. Props a -> Number -> a -> VNode
calculateRowView { rowView } rowHeight row =
  let style = "height: " <> show rowHeight <> "px;"
   in rowView { style, row }

padding :: Number -> VNode
padding height =
  H.div # H.style ("height: " <> show height <> "px;")
