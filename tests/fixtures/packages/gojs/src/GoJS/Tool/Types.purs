module GoJS.Tool.Types where

import Prelude

import Data.Maybe (Maybe(..))
import GoJS.Unsafe.InstanceOf (isInstanceOf)
import Unsafe.Coerce (unsafeCoerce)

class IsTool (t :: Type) where
  fromTool :: Tool_ -> Maybe t

-- | Tool types.
foreign import data ActionTool_ :: Type
foreign import data ClickCreatingTool_ :: Type
foreign import data ClickSelectingTool_ :: Type
foreign import data ContextMenuTool_ :: Type
foreign import data DragSelectingTool_ :: Type
foreign import data DraggingTool_ :: Type
foreign import data LinkReshapingTool_ :: Type
foreign import data LinkingTool_ :: Type
foreign import data PanningTool_ :: Type
foreign import data RelinkingTool_ :: Type
foreign import data ResizingTool_ :: Type
foreign import data RotatingTool_ :: Type
foreign import data TextEditingTool_ :: Type
foreign import data ToolManager_ :: Type -- A special tool that manages all other tools.
foreign import data Tool_ :: Type -- A type representing an abstract tool, convertible to any concrete tool type.

instance IsTool ClickCreatingTool_ where
  fromTool x 
    | isInstanceOf x "ClickCreatingTool" = Just (unsafeCoerce x)
    | otherwise = Nothing
instance IsTool ActionTool_ where
  fromTool x 
    | isInstanceOf x "ActionTool" = Just (unsafeCoerce x)
    | otherwise = Nothing
instance IsTool ClickSelectingTool_ where
  fromTool x 
    | isInstanceOf x "ClickSelectingTool" = Just (unsafeCoerce x)
    | otherwise = Nothing
instance IsTool ContextMenuTool_ where
  fromTool x 
    | isInstanceOf x "ContextMenuTool" = Just (unsafeCoerce x)
    | otherwise = Nothing
instance IsTool DragSelectingTool_ where
  fromTool x 
    | isInstanceOf x "DragSelectingTool" = Just (unsafeCoerce x)
    | otherwise = Nothing
instance IsTool DraggingTool_ where
  fromTool x 
    | isInstanceOf x "DraggingTool" = Just (unsafeCoerce x)
    | otherwise = Nothing
instance IsTool LinkReshapingTool_ where
  fromTool x 
    | isInstanceOf x "LinkReshapingTool" = Just (unsafeCoerce x)
    | otherwise = Nothing
instance IsTool LinkingTool_ where
  fromTool x 
    | isInstanceOf x "LinkingTool" = Just (unsafeCoerce x)
    | otherwise = Nothing
instance IsTool PanningTool_ where
  fromTool x 
    | isInstanceOf x "PanningTool" = Just (unsafeCoerce x)
    | otherwise = Nothing
instance IsTool RelinkingTool_ where
  fromTool x 
    | isInstanceOf x "RelinkingTool" = Just (unsafeCoerce x)
    | otherwise = Nothing
instance IsTool ResizingTool_ where
  fromTool x 
    | isInstanceOf x "ResizingTool" = Just (unsafeCoerce x)
    | otherwise = Nothing
instance IsTool RotatingTool_ where
  fromTool x 
    | isInstanceOf x "RotatingTool" = Just (unsafeCoerce x)
    | otherwise = Nothing
instance IsTool TextEditingTool_ where
  fromTool x 
    | isInstanceOf x "TextEditingTool" = Just (unsafeCoerce x)
    | otherwise = Nothing


foreign import data HTMLInfo_ :: Type