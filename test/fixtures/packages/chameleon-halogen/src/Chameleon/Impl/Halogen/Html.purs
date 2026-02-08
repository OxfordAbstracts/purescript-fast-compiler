module Chameleon.Impl.Halogen.Html
  ( HalogenHtml
  , runHalogenHtml
  ) where

import Prelude

import Data.Bifunctor (bimap, lmap)
import Data.Maybe (Maybe(..))
import Data.String as Str
import Data.Tuple.Nested (type (/\), (/\))
import Foreign (Foreign)
import Foreign.Object (Object)
import Foreign.Object as Object
import Halogen.HTML (HTML(..), Namespace(..))
import Halogen.HTML as HA
import Halogen.HTML as HH
import Halogen.HTML.Properties (IProp(..))
import Halogen.HTML.Properties as HP
import Halogen.Query.Input (Input(..))
import Halogen.VDom (VDom)
import Halogen.VDom as HVD
import Halogen.VDom.DOM.Prop as H
import Halogen.VDom.DOM.Prop as HVDP
import Safe.Coerce (coerce)
import Unsafe.Coerce (unsafeCoerce)
import Chameleon (class Html, class MapMaybe, ElemName(..), Key(..), Prop(..))
import Web.Event.Event (EventType(..))
import Web.Event.Event as Web
import Web.Event.Internal.Types as DOM

--------------------------------------------------------------------------------
-- HalogenHtml
--------------------------------------------------------------------------------

newtype HalogenHtml a = HalogenHtml (HTML Void a)

derive instance Functor HalogenHtml

instance MapMaybe HalogenHtml where
  mapMaybe :: forall msg1 msg2. (msg1 -> Maybe msg2) -> HalogenHtml msg1 -> HalogenHtml msg2
  mapMaybe f (HalogenHtml (HTML vdom)) = HalogenHtml (HTML $ go vdom)
    where
    go :: VDom (Array (H.Prop (Input msg1))) Void -> VDom (Array (H.Prop (Input msg2))) Void
    go = case _ of
      HVD.Elem ns name props xs -> HVD.Elem ns name (map convertProp props) (map go xs)
      HVD.Keyed ns name props xs -> HVD.Keyed ns name (map convertProp props) (map (map go) xs)
      HVD.Text str -> HVD.Text str
      HVD.Widget x -> absurd x
      HVD.Grafted g -> HVD.Grafted $ bimap (map convertProp) identity g

    convertProp :: H.Prop (Input msg1) -> H.Prop (Input msg2)
    convertProp = case _ of
      HVDP.Handler type_ cb ->
        let
          newCb :: Web.Event -> Maybe (Input msg2)
          newCb ev = do
            result :: Input msg1 <- cb ev
            convertInput result
        in
          HVDP.Handler type_ newCb
      HVDP.Ref _ -> HVDP.Ref (const Nothing)
      HVDP.Attribute x y z -> HVDP.Attribute x y z
      HVDP.Property x y -> HVDP.Property x y

    convertInput :: Input msg1 -> Maybe (Input msg2)
    convertInput = case _ of
      Action msg -> f msg <#> \msg' -> Action msg'
      RefUpdate x y -> Just $ RefUpdate x y

instance Html HalogenHtml where

  elem (ElemName name) props children = HalogenHtml $
    (mkElemFn name)
      (HH.ElemName name)
      (mapProp <$> props)
      (coerce children)

  elemKeyed (ElemName name) props children = HalogenHtml $
    (mkElemFnKeyed name)
      (HH.ElemName name)
      (mapProp <$> props)
      ((\(Key key /\ html) -> key /\ runHalogenHtml html) <$> children)

  text str = HalogenHtml $ HH.text str

mkElemFn :: forall r w i. String -> HH.ElemName -> Array (IProp r i) -> Array (HTML w i) -> HTML w i
mkElemFn name =
  if isSvgElem name then HH.elementNS (Namespace "http://www.w3.org/2000/svg")
  else HH.element

mkElemFnKeyed :: forall r w i. String -> HH.ElemName -> Array (IProp r i) -> Array (String /\ HTML w i) -> HTML w i
mkElemFnKeyed name =
  if isSvgElem name then HH.keyedNS (Namespace "http://www.w3.org/2000/svg")
  else HH.keyed

mapProp :: forall r a. Prop a -> IProp r a
mapProp prop = case prop of
  Attr k v | isHalogenAttr k -> HP.attr (HA.AttrName k) v
  Attr k v -> HP.prop (HH.PropName k) v
  Event n h -> IProp $ HH.handler (EventType $ Str.toLower n) (eventToForeign >>> h >>> map Action)

isHalogenAttr :: String -> Boolean
isHalogenAttr str =
  let
    isDataAttrib :: Boolean
    isDataAttrib = Str.stripPrefix (Str.Pattern "data-") str /= Nothing

    isListed :: Boolean
    isListed = Object.member str attribs
  in
    isListed || isDataAttrib

eventToForeign :: DOM.Event -> Foreign
eventToForeign = unsafeCoerce

runHalogenHtml :: forall b a. HalogenHtml a -> HTML b a
runHalogenHtml (HalogenHtml html) = lmap absurd $ html

attribs :: Object Unit
attribs = Object.fromFoldable $ map (\x -> x /\ unit)
  [ "attributeName"
  , "begin"
  , "class_"
  , "classes"
  , "cx"
  , "cy"
  , "d"
  , "dominantBaseline"
  , "dur"
  , "fill"
  , "fillAnim"
  , "fillOpacity"
  , "fontFamily"
  , "fontSize"
  , "fontSizeAdjust"
  , "fontStretch"
  , "fontStyle"
  , "fontVariant"
  , "fontWeight"
  , "from"
  , "to"
  , "id"
  , "maxlength"
  , "minlength"
  , "markerStart"
  , "markerMid"
  , "markerEnd"
  , "markerUnits"
  , "markerWidth"
  , "markerHeight"
  , "mask"
  , "maskUnits"
  , "maskContentUnits"
  , "orient"
  , "path"
  , "points"
  , "pathLength"
  , "patternContentUnits"
  , "patternTransform"
  , "patternUnits"
  , "preserveAspectRatio"
  , "r"
  , "refX"
  , "refY"
  , "repeatCount"
  , "rx"
  , "ry"
  , "style"
  , "stroke"
  , "strokeDashArray"
  , "strokeDashOffset"
  , "strokeLineCap"
  , "strokeLineJoin"
  , "strokeMiterLimit"
  , "strokeOpacity"
  , "stroke-width"
  , "textAnchor"
  , "transform"
  , "viewBox"
  , "width"
  , "height"
  , "x"
  , "y"
  , "x1"
  , "y1"
  , "x2"
  , "y2"
  , "href"
  , "xmlns"
  , "values"
  , "keyTimes"
  ]

isSvgElem :: String -> Boolean
isSvgElem str = Object.member str svgElems

svgElems :: Object Unit
svgElems = Object.fromFoldable $ map (\x -> x /\ unit)
  [ "element"
  , "svg"
  , "g"
  , "circle"
  , "image"
  , "ellipse"
  , "rect"
  , "path"
  , "pattern"
  , "line"
  , "polyline"
  , "polygon"
  , "text"
  , "foreignObject"
  , "defs"
  , "mask"
  , "marker"
  , "animate"
  , "animateMotion"
  , "circleNode"
  , "mpath"
  , "title"
  , "use"
  ]
