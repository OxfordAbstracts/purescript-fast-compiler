module GoJS.GraphObject.Types where

import Prelude

import Data.Maybe (Maybe(..))
import GoJS.Tool.Types (HTMLInfo_)
import GoJS.Unsafe.InstanceOf (isInstanceOf)
import Unsafe.Coerce (unsafeCoerce)

-- | GraphObject types
foreign import data GraphObject_ :: Type -- Has no constructor
foreign import data Shape_ :: Type
foreign import data Picture_ :: Type
foreign import data TextBlock_ :: Type
foreign import data Placeholder_ :: Type
foreign import data Panel_ :: Type
foreign import data Button_ :: Type
foreign import data Part_ :: Type
foreign import data Adornment_ :: Type
foreign import data Node_ :: Type
foreign import data Link_ :: Type
foreign import data Group_ :: Type
class IsGraphObject (a :: Type)

instance IsGraphObject GraphObject_
instance IsGraphObject Shape_
instance IsGraphObject Placeholder_
instance IsGraphObject TextBlock_
instance IsGraphObject Picture_
instance IsGraphObject Panel_
instance IsGraphObject Button_ -- Buttons are really just panels
instance IsGraphObject Part_
instance IsGraphObject Node_
instance IsGraphObject Group_
instance IsGraphObject Link_
instance IsGraphObject Adornment_

class IsGraphObject a <= IsPanel a where
  fromPanel :: Panel_ -> Maybe a
instance IsPanel Panel_ where
  fromPanel = Just
instance IsPanel Button_ where -- Buttons are really just panels
  fromPanel = Just <<< unsafeCoerce
instance IsPanel Part_ where
  fromPanel x 
    | isInstanceOf x "Part" = Just (unsafeCoerce x)
    | otherwise = Nothing
instance IsPanel Node_ where
  fromPanel x 
    | isInstanceOf x "Node" = Just (unsafeCoerce x)
    | otherwise = Nothing
instance IsPanel Group_ where
  fromPanel x 
    | isInstanceOf x "Group" = Just (unsafeCoerce x)
    | otherwise = Nothing
instance IsPanel Link_ where
  fromPanel x 
    | isInstanceOf x "Link" = Just (unsafeCoerce x)
    | otherwise = Nothing
instance IsPanel Adornment_ where
  fromPanel x 
    | isInstanceOf x "Adornment" = Just (unsafeCoerce x)
    | otherwise = Nothing

class IsPanel a <= IsPart a where
  fromPart :: Part_ -> Maybe a
instance IsPart Part_ where
  fromPart = Just
instance IsPart Node_ where
  fromPart x 
    | isInstanceOf x "Node" = Just (unsafeCoerce x)
    | otherwise = Nothing
instance IsPart Group_ where
  fromPart x 
    | isInstanceOf x "Group" = Just (unsafeCoerce x)
    | otherwise = Nothing
instance IsPart Link_ where
  fromPart x 
    | isInstanceOf x "Link" = Just (unsafeCoerce x)
    | otherwise = Nothing
instance IsPart Adornment_ where
  fromPart x 
    | isInstanceOf x "Adornment" = Just (unsafeCoerce x)
    | otherwise = Nothing
class IsPart a <= IsNode a where
  fromNode :: Node_ -> Maybe a
instance IsNode Node_ where
  fromNode = Just
instance IsNode Group_ where
  fromNode x 
    | isInstanceOf x "Group" = Just (unsafeCoerce x)
    | otherwise = Nothing

data ContextMenu_
  = AdornmentContextMenu Adornment_
  | HTMLInfoContextMenu HTMLInfo_

toContextMenu :: forall a. a -> Maybe ContextMenu_
toContextMenu x
  | isInstanceOf x "Adornment" = Just (AdornmentContextMenu (unsafeCoerce x))
  | isInstanceOf x "HTMLInfo" = Just (HTMLInfoContextMenu (unsafeCoerce x))
  | otherwise = Nothing