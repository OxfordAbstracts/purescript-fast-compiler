module Data.Text.Diff where

import Prelude

import Effect.Class (class MonadEffect, liftEffect)
import Effect.Exception (Error, throw)

import Control.Monad.Error.Class (class MonadError, class MonadThrow, try)

import Data.String as String
import Data.Maybe (Maybe(..))
import Data.Array (catMaybes, take, length) as Array
-- import Data.Text.Format (of_)
import Data.Tuple (Tuple)
import Data.Tuple (fst, snd) as Tuple
import Data.Tuple.Nested ((/\), type (/\))
import Data.Bifunctor (bimap)
import Data.These (these, These(..), theseLeft, theseRight)
import Data.Align (class Align, aligned, crosswalk)



class Eq a <= Diffable a where
    toDiffString :: a -> String


data DiffSide a
    = New a
    | Changed a
    | Equal a
    | Absent


data DiffLine a
    = NewLeft a
    | NewRight a
    | BothEqual a
    | Different a a


derive instance Eq a => Eq (DiffSide a)
derive instance Eq a => Eq (DiffLine a)
derive instance Functor DiffSide
derive instance Functor DiffLine


prefixes =
    { left : ">>"
    , right : "<<"
    , eq : ".."
    , add : "++"
    , sub : "--"
    }


fromThese :: forall a. Eq a => These a a -> DiffLine a
fromThese = case _ of
    This l -> NewLeft l
    That r -> NewRight r
    Both l r ->
        if l == r then BothEqual l
        else Different l r


left :: forall a. DiffLine a -> DiffSide a
left = case _ of
    NewLeft l -> New l
    NewRight _ -> Absent
    BothEqual l -> Equal l
    Different l _ -> Changed l


right :: forall a. DiffLine a -> DiffSide a
right = case _ of
    NewLeft _ -> Absent
    NewRight r -> New r
    BothEqual r -> Equal r
    Different _ r -> Changed r


data Limit
    = NoLimit
    | Limit Int


data Comparator
    = Stack Limit
    | Zip Limit
    | OnlyDifferent Limit
    | Plain
    | Silent


compareBy :: forall m. MonadEffect m => MonadThrow Error m => Comparator -> (String -> String -> m Unit)
compareBy (Stack limit) = diffStackCompare' limit
compareBy (Zip limit) = diffCompare' limit
compareBy (OnlyDifferent limit) = onlyDifferentCompare' limit
compareBy Plain  = \sA sB -> when (sA /= sB) $ liftEffect $ throw $ show sA <> " ≠ " <> show sB
compareBy Silent = \sA sB -> when (sA /= sB) $ liftEffect $ throw "x"


diffCompare
  :: forall m t
   . MonadEffect m
  => MonadThrow Error m
  => Diffable t
  => t
  -> t
  -> m Unit
diffCompare =
    diffCompare' NoLimit


diffCompare'
  :: forall m t
   . MonadEffect m
  => MonadThrow Error m
  => Diffable t
  => Limit
  -> t
  -> t
  -> m Unit
diffCompare' limit v1 v2 =
  when (v1 /= v2) $
    liftEffect $ throw $ lineByLineComparison limit (toDiffString v1) (toDiffString v2)


diffStackCompare
  :: forall m t
   . MonadEffect m
  => MonadThrow Error m
  => Diffable t
  => t
  -> t
  -> m Unit
diffStackCompare =
  diffStackCompare' NoLimit


diffStackCompare'
  :: forall m t
   . MonadEffect m
  => MonadThrow Error m
  => Diffable t
  => Limit
  -> t
  -> t
  -> m Unit
diffStackCompare' limit v1 v2 =
  when (v1 /= v2) $
    liftEffect $ throw $ twoStacksComparison limit (toDiffString v1) (toDiffString v2)


onlyDifferentCompare
  :: forall m t
   . MonadEffect m
  => MonadThrow Error m
  => Diffable t
  => t
  -> t
  -> m Unit
onlyDifferentCompare =
  onlyDifferentCompare' NoLimit


onlyDifferentCompare'
  :: forall m t
   . MonadEffect m
  => MonadThrow Error m
  => Diffable t
  => Limit
  -> t
  -> t
  -> m Unit
onlyDifferentCompare' limit v1 v2 =
  when (v1 /= v2) $
    liftEffect $ throw $ onlyDiffsComparison limit (toDiffString v1) (toDiffString v2)


lineByLineComparison :: Limit -> String -> String -> String
lineByLineComparison limit a b =
    let
        comparedLines = compareByLines a b
        (adjustedLines /\ linesLeft) = _adjustByLimit limit comparedLines
    in
        case linesLeft of
            NoneLeft -> String.joinWith "\n" $ toDiffString <$> comparedLines
            LinesLeft n ->
                (String.joinWith "\n" $ toDiffString <$> adjustedLines)
                <> "\n... "<> show n <> " lines more."


onlyDiffsComparison :: Limit -> String -> String -> String
onlyDiffsComparison limit a b =
    let
        comparison = compareByLines a b
        formatLeft = case _ of
            New l     -> Just $ prefixes.add <> " " <> l
            Absent    -> Nothing
            Equal _   -> Nothing
            Changed l -> Just $ prefixes.left <> " " <> l
        formatRight = case _ of
            New r     -> Just $ prefixes.sub <> " " <> r
            Absent    -> Nothing
            Equal _   -> Nothing
            Changed r -> Just $ prefixes.right <> " " <> r
        (formattedA /\ leftA) = _adjustByLimit limit $ Array.catMaybes $ formatLeft  <$> left  <$> comparison
        (formattedB /\ leftB) = _adjustByLimit limit $ Array.catMaybes $ formatRight <$> right <$> comparison
    in
           (String.joinWith "\n" formattedA)
        <> "\n---------------------------------------------------------------\n"
        <> (String.joinWith "\n" formattedB)
        <> _linesLeftText leftA leftB


twoStacksComparison :: Limit -> String -> String -> String
twoStacksComparison limit a b =
    let
        comparison = compareByLines a b
        formatLeft = case _ of
            New l     -> Just $ prefixes.add <> " " <> l
            Absent    -> Nothing
            Equal l   -> Just $ prefixes.eq <> " " <> l
            Changed l -> Just $ prefixes.left <> " " <> l
        formatRight = case _ of
            New r     -> Just $ prefixes.sub <> " " <> r
            Absent    -> Nothing
            Equal r   -> Just $ prefixes.eq <> " " <> r
            Changed r -> Just $ prefixes.right <> " " <> r
        (formattedA /\ leftA) = _adjustByLimit limit $ Array.catMaybes $ formatLeft  <$> left  <$> comparison
        (formattedB /\ leftB) = _adjustByLimit limit $ Array.catMaybes $ formatRight <$> right <$> comparison
    in
           (String.joinWith "\n" $ formattedA)
        <> "\n---------------------------------------------------------------\n"
        <> (String.joinWith "\n" $ formattedB)
        <> _linesLeftText leftA leftB


compareMany :: forall f a. Eq a => Align f => f a -> f a -> f (DiffLine a)
compareMany as bs = fromThese <$> aligned as bs


data LinesLeft
    = NoneLeft
    | LinesLeft Int


_linesLeftText :: LinesLeft -> LinesLeft -> String
_linesLeftText NoneLeft NoneLeft = ""
_linesLeftText (LinesLeft n) NoneLeft | n <= 0 = ""
_linesLeftText NoneLeft (LinesLeft n) | n <= 0 = ""
_linesLeftText (LinesLeft n) NoneLeft = "\n..." <> show n <> " lines more on the left side."
_linesLeftText NoneLeft (LinesLeft n) = "\n..." <> show n <> " lines more on the right side."
_linesLeftText (LinesLeft nA) (LinesLeft nB) =
    if (nA > 0) || (nB > 0) then
        if (nA == nB)
            then "\n..." <> show nA <> " lines more on both sides."
            else
                "\n..." <> show nA <> " lines more on the left side" <>
                "\n..." <> show nB <> " lines more on the right side."
    else
        ""


_adjustByLimit :: forall a. Limit -> Array a -> (Array a /\ LinesLeft)
_adjustByLimit NoLimit source = source /\ NoneLeft
_adjustByLimit (Limit n) source =
    let
        adjusted = Array.take n source
    in
        adjusted /\ (LinesLeft $ Array.length source - Array.length adjusted)


compareByLines :: String -> String -> Array (DiffLine String)
compareByLines a b =
    let
        linesA = String.split (String.Pattern "\n") a
        linesB = String.split (String.Pattern "\n") b
    in compareMany linesA linesB


instance Diffable String where
    toDiffString = identity


instance Diffable Int where
    toDiffString = show


instance (Diffable a, Diffable b) => Diffable (These a b) where
    toDiffString = bimap toDiffString toDiffString >>>
        these
            (\lA -> prefixes.add <> " " <> lA)
            (\lB -> prefixes.sub <> " " <> lB)
            (\lA lB ->
                if lA == lB then prefixes.eq <> " " <> lA
                else prefixes.left <> " " <> lA <> "\n" <> prefixes.right <> " " <> lB
            )


instance (Eq a, Diffable a) => Diffable (DiffLine a) where
    toDiffString = map toDiffString >>> case _ of
        NewLeft lA      -> prefixes.add  <> " " <> lA
        NewRight lB     -> prefixes.sub  <> " " <> lB
        BothEqual lA    -> prefixes.eq   <> " " <> lA
        Different lA lB -> prefixes.left <> " " <> lA <> "\n" <> prefixes.right <> " " <> lB


instance (Diffable a, Diffable b) => Diffable (Tuple a b) where
    toDiffString tpl = toDiffString (Tuple.fst tpl) <> "\n" <> toDiffString (Tuple.snd tpl)

instance Diffable a => Diffable (Array a) where
    toDiffString arr = String.joinWith "\n" $ toDiffString <$> arr
