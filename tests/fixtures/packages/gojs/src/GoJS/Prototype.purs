module GoJS.Prototype where

import Prelude

import Data.Nullable (Nullable)
import Data.Symbol (reflectSymbol)
import Effect (Effect)
import GoJS.Class (class ClassName)
import GoJS.Diagram.Types (class IsDiagram)
import GoJS.GraphObject.Types (Node_)
import GoJS.Geometry.Types (Point_)
import GoJS.Layout.Types (class IsLayout, class LayoutNetwork, CircularLayout_, ForceDirectedLayout_, LayeredDigraphLayout_, TreeLayout_)
import GoJS.Tool.Types (class IsTool)
import GoJS.Unsafe.Prototype (prototypeArity0_, prototypeArity1_, prototypeArity2_)
import Type.Prelude (Proxy(..))

class
  ( ClassName this className
  ) <=
  Prototype
    (className :: Symbol)
    (methodName :: Symbol)
    (this :: Type)
    (fn :: Type)
  | this -> className, className -> this, methodName -> fn where
  prototype' :: Proxy className -> Proxy methodName -> (this -> fn)

instance Prototype "TreeLayout" "commitNodes" TreeLayout_ (Effect Unit) where
  prototype' className methodName = prototypeArity0_ (reflectSymbol className) (reflectSymbol methodName)

instance Prototype "ForceDirectedLayout" "commitNodes" ForceDirectedLayout_ (Effect Unit) where
  prototype' className methodName = prototypeArity0_ (reflectSymbol className) (reflectSymbol methodName)

instance Prototype "LayeredDigraphLayout" "commitNodes" LayeredDigraphLayout_ (Effect Unit) where
  prototype' className methodName = prototypeArity0_ (reflectSymbol className) (reflectSymbol methodName)

instance Prototype "CircularLayout" "commitNodes" CircularLayout_ (Effect Unit) where
  prototype' className methodName = prototypeArity0_ (reflectSymbol className) (reflectSymbol methodName)

instance (IsLayout l, ClassName l className) => Prototype className "commitLayout" l (Effect Unit) where
  prototype' className methodName = prototypeArity0_ (reflectSymbol className) (reflectSymbol methodName)

instance (IsLayout l, ClassName l className) => Prototype className "assignLayers" l (Effect Unit) where
  prototype' className methodName = prototypeArity0_ (reflectSymbol className) (reflectSymbol methodName)

instance (LayoutNetwork l n e v, ClassName l className, IsDiagram d) => Prototype className "makeNetwork" l (d -> Effect n) where
  prototype' className methodName = prototypeArity1_ (reflectSymbol className) (reflectSymbol methodName)

instance (LayoutNetwork l n e v, ClassName l className) => Prototype className "nodeMinColumnSpace" l (v -> Boolean -> Effect Number) where
  prototype' className methodName = prototypeArity2_ (reflectSymbol className) (reflectSymbol methodName)

instance (LayoutNetwork l n e v, ClassName l className) => Prototype className "nodeMinLayerSpace" l (v -> Boolean -> Effect Number) where
  prototype' className methodName = prototypeArity2_ (reflectSymbol className) (reflectSymbol methodName)

instance (IsTool t, ClassName t toolName) => Prototype toolName "insertPart" t (Point_ -> Effect (Nullable Node_)) where
  prototype' className methodName = prototypeArity1_ (reflectSymbol className) (reflectSymbol methodName)

prototype :: forall className @methodName this rest. Prototype className methodName this rest => this -> rest
prototype = prototype' (Proxy @className) (Proxy @methodName)