module Chameleon.Styled.Core
  ( Anim
  , ClassName(..)
  , ElemName(..)
  , ElemScope(..)
  , InlineStyle(..)
  , Style
  , StyleDecl
  , StyleMap
  , StyleT
  , anim
  , class HtmlStyled
  , class IsDecl
  , class IsStyle
  , decl
  , declWith
  , mergeDecl
  , registerStyleMap
  , runStyleT
  , styleKeyedLeaf
  , styleKeyedLeafNamed
  , styleKeyedNode
  , styleKeyedNodeNamed
  , styleLeaf
  , styleLeafNamed
  , styleNode
  , styleNodeNamed
  , toStyle
  ) where

import Prelude

import Chameleon (class Html, class MapMaybe, Prop(..))
import Chameleon as C
import Chameleon.Class as VDC
import Chameleon.HTML.Attributes as VP
import Chameleon.HTML.Elements as VDE
import Chameleon.Transformers.Accum.Class (class Accum, class TellAccum, censorAccum, tellAccum)
import Chameleon.Transformers.Accum.Trans (AccumT(..), runAccumT)
import Chameleon.Transformers.Ctx.Trans (CtxT(..))
import Chameleon.Transformers.FunctorTrans.Class (class FunctorTrans)
import Chameleon.Transformers.FunctorTrans.Class as FT
import Chameleon.Transformers.OutMsg.Class (class OutMsg, class RunOutMsg, fromOutHtml, runOutMsg)
import Chameleon.Types (ElemKeyedNode, ElemLeaf, ElemNode, ElemKeyedLeaf)
import Data.Array as Array
import Data.Foldable (fold, foldr)
import Data.HashMap (HashMap)
import Data.HashMap as HashMap
import Data.Hashable (class Hashable, hash)
import Data.Int as Int
import Data.Maybe (Maybe(..), isJust)
import Data.Newtype (class Newtype, unwrap)
import Data.Ord (abs)
import Data.String (Pattern(..), Replacement(..))
import Data.String as Str
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested (type (/\), (/\))

class IsStyle a where
  toStyle :: a -> Style

newtype InlineStyle = InlineStyle String

newtype ClassName = ClassName String

newtype StyleDecl = StyleDecl (Array (Maybe Selector /\ Array String))

newtype Selector = Selector String

newtype Style = Style
  { inline :: Array InlineStyle
  , classes :: Array ClassName
  , declarations :: Array StyleDecl
  , animations :: Array Anim
  }

newtype AnimName = AnimName String

newtype HashedAnimName = HashedAnimName String

newtype AnimDecl = AnimDecl (Array AnimStep)

newtype Anim = Anim (AnimName /\ AnimDecl)

newtype AnimStep = AnimStep (String /\ Array String)

newtype ElemName = ElemName String

newtype ElemScope = ElemScope String

-------------------------------------------------------------------------------
-- StyleMap
-------------------------------------------------------------------------------

class Html html <= HtmlStyled (html :: Type -> Type) where
  registerStyleMap :: forall msg. StyleMap -> html msg -> html msg

newtype StyleMap = StyleMap { anim :: AnimMap, decl :: DeclMap }

type DeclMap = HashMap ClassName StyleDecl

type AnimMap = HashMap HashedAnimName AnimDecl

replaceIds :: HashMap String String -> StyleDecl -> StyleDecl
replaceIds replaceMap (StyleDecl styleDecls) =
  StyleDecl (map replaceEntry styleDecls)

  where
  replaceEntry :: Maybe Selector /\ Array String -> Maybe Selector /\ Array String
  replaceEntry (selector /\ strs) =
    selector /\ map (replaceByMap replaceMap) strs

getStyleMap :: Maybe ElemName -> Style -> StyleMap /\ Style
getStyleMap elemName style@(Style { declarations, animations }) =
  styleMap /\ newStyle
  where
  styleMap :: StyleMap
  styleMap = StyleMap
    { decl: declMap
    , anim: animMap
    }

  animInfo :: Array (HashedAnimName /\ AnimName /\ AnimDecl)
  animInfo = animations
    # map
        ( \(Anim (animName /\ animDecl)) ->
            mkHashedAnimName animDecl /\ animName /\ animDecl
        )

  declMap :: DeclMap
  declMap = HashMap.fromArrayBy mkClassName identity declarationsReplaced

  declarationsReplaced :: Array StyleDecl
  declarationsReplaced = map (replaceIds animReplaceMap) declarations

  animMap :: AnimMap
  animMap =
    HashMap.fromArrayBy
      (\(key /\ _) -> key)
      (\(_ /\ _ /\ value) -> value)
      animInfo

  animReplaceMap :: HashMap String String
  animReplaceMap =
    HashMap.fromArrayBy
      (\(_ /\ AnimName animName /\ _) -> "$" <> animName)
      (\(HashedAnimName hashedAnimName /\ _ /\ _) -> hashedAnimName)
      animInfo

  mkHashedAnimName :: AnimDecl -> HashedAnimName
  mkHashedAnimName animDecl = HashedAnimName (prefixAnim <> niceHash animDecl)

  mkClassName :: StyleDecl -> ClassName
  mkClassName styleDecl = ClassName (prefix <> niceHash styleDecl)

  newStyle :: Style
  newStyle =
    let
      StyleMap { decl } = styleMap
    in
      style
        # \(Style rec) -> Style $ rec
            { declarations = []
            , classes = HashMap.keys decl
            }

  prefix =
    ( case elemName of
        Just (ElemName elemName') -> elemName'
        Nothing -> "hashed"
    ) <> "-"

  prefixAnim = prefix <> "-anim-"

niceHash :: forall a. Hashable a => a -> String
niceHash val =
  let
    numericHash :: Int
    numericHash = hash val

    stringHash :: String
    stringHash =
      if numericHash < 0 then
        show (abs numericHash) <> "0"
      else
        show numericHash <> "1"

    fixedLength :: Int
    fixedLength = 10

    length :: Int
    length = Str.length stringHash

    times :: Int
    times = Int.ceil (Int.toNumber fixedLength / Int.toNumber length)
  in
    Array.replicate times stringHash
      # fold
      # Str.take fixedLength

printStyleMap :: StyleMap -> String
printStyleMap (StyleMap styleMap) =
  printDeclMap styleMap.decl <> "\n\n" <> printAnimMap styleMap.anim

printAnimMap :: AnimMap -> String
printAnimMap animMap =
  HashMap.toArrayBy printEntry animMap
    # Str.joinWith "\n"

  where
  printEntry :: HashedAnimName -> AnimDecl -> String
  printEntry (HashedAnimName animName) (AnimDecl animSteps) =
    Str.joinWith "\n"
      [ "@keyframes " <> animName <> " {"
      , Str.joinWith "\n" (map printAnimStep animSteps)
      , "}"
      ]

  printAnimStep :: AnimStep -> String
  printAnimStep (AnimStep (stepName /\ strs)) =
    Str.joinWith "\n"
      [ stepName <> " {"
      , Str.joinWith ";" strs
      , "}"
      ]

printDeclMap :: DeclMap -> String
printDeclMap declMap =
  HashMap.toArrayBy printEntry declMap
    # join
    # Str.joinWith "\n"

  where
  printEntry :: ClassName -> StyleDecl -> Array String
  printEntry className (StyleDecl styleDecls) =
    map (printScopedEntry className) styleDecls

  printScopedEntry :: ClassName -> Maybe Selector /\ Array String -> String
  printScopedEntry (ClassName className) (selector /\ styleDecl) =
    Str.joinWith ""
      [ "."
      , className
      , case selector of
          Nothing -> ""
          Just (Selector str) -> str
      , " {\n"
      , Str.joinWith "\n" (map (_ <> ";") styleDecl)
      , "\n}"
      ]

foldStyleMaps :: Array StyleMap -> StyleMap
foldStyleMaps = foldr next init
  where
  next :: StyleMap -> StyleMap -> StyleMap
  next (StyleMap styleMap1) (StyleMap styleMap2) = StyleMap
    { anim: HashMap.union styleMap1.anim styleMap2.anim
    , decl: HashMap.union styleMap1.decl styleMap2.decl
    }

  init :: StyleMap
  init = StyleMap { anim: HashMap.empty, decl: HashMap.empty }

viewStylemap :: forall html msg. Html html => StyleMap -> html msg
viewStylemap styleMap =
  VDE.style_ [ VDC.text $ printStyleMap styleMap ]

decl :: forall decl. IsDecl decl => decl -> StyleDecl
decl dec = StyleDecl [ Nothing /\ [ mergeDecl dec ] ]

declWith :: forall decl. IsDecl decl => String -> decl -> StyleDecl
declWith selector dec = StyleDecl
  [ Just (Selector selector) /\ [ mergeDecl dec ] ]

anim :: String -> Array (String /\ Array String) -> Anim
anim animName steps = Anim
  ( AnimName animName /\
      AnimDecl (map (\(stepName /\ strs) -> AnimStep (stepName /\ strs)) steps)
  )

-------------------------------------------------------------------------------
-- Impl
-------------------------------------------------------------------------------

newtype StyleT html a = StyleT (AccumT (Array StyleMap) html a)

instance FunctorTrans StyleT where
  lift :: forall html a. Functor html => html a -> StyleT html a
  lift html = StyleT $ FT.lift html

derive instance (Functor html) => Functor (StyleT html)

derive newtype instance (Html html) => Html (StyleT html)

derive newtype instance (Html html) => MapMaybe (StyleT html)

instance Html html => HtmlStyled (StyleT html) where
  registerStyleMap styleMap (StyleT accumT) =
    StyleT $ tellAccum [ styleMap ] accumT

runStyleT :: forall html a. Html html => StyleT html a -> html a
runStyleT (StyleT accumT) =
  let
    html /\ styleMaps = runAccumT accumT
  in
    C.div_
      [ viewStylemap (foldStyleMaps styleMaps)
      , html
      ]

instance (TellAccum acc html) => TellAccum acc (StyleT html) where
  tellAccum acc (StyleT (AccumT styleMaps html)) = StyleT $ (AccumT styleMaps (tellAccum acc html))

instance (Accum acc html) => Accum acc (StyleT html) where
  censorAccum f (StyleT (AccumT styleMaps html)) = StyleT $ (AccumT styleMaps (censorAccum f html))

instance (OutMsg out html) => OutMsg out (StyleT html) where
  fromOutHtml (StyleT (AccumT styleMaps html)) = StyleT $ (AccumT styleMaps (fromOutHtml html))

instance (RunOutMsg out html) => RunOutMsg out (StyleT html) where
  runOutMsg (StyleT (AccumT styleMaps html)) = StyleT $ (AccumT styleMaps (runOutMsg html))

---

instance (HtmlStyled html) => HtmlStyled (CtxT ctx html) where
  registerStyleMap styleMap (CtxT mkHtml) = CtxT
    \ctx -> registerStyleMap styleMap $ mkHtml ctx

-------------------------------------------------------------------------------
-- Style Elements
-------------------------------------------------------------------------------

styleNode
  :: forall html style a
   . Html html
  => HtmlStyled html
  => IsStyle style
  => ElemNode html a
  -> style
  -> ElemNode html a
styleNode =
  styleNodeNamed Nothing Nothing

styleNodeNamed
  :: forall html style a
   . Html html
  => HtmlStyled html
  => IsStyle style
  => Maybe ElemName
  -> Maybe ElemScope
  -> ElemNode html a
  -> style
  -> ElemNode html a
styleNodeNamed elemName elemScope elem someStyle props children =
  registerStyleMap styleMap $
    elem
      (addIds elemName elemScope $ addStyle newStyle props)
      children
  where
  oldStyle = toStyle someStyle
  styleMap /\ newStyle = getStyleMap elemName oldStyle

styleLeaf
  :: forall html style a
   . Html html
  => HtmlStyled html
  => IsStyle style
  => ElemLeaf html a
  -> style
  -> ElemLeaf html a
styleLeaf =
  styleLeafNamed Nothing Nothing

styleLeafNamed
  :: forall html style a
   . Html html
  => HtmlStyled html
  => IsStyle style
  => Maybe ElemName
  -> Maybe ElemScope
  -> ElemLeaf html a
  -> style
  -> ElemLeaf html a
styleLeafNamed elemName elemScope elem someStyle props =
  registerStyleMap styleMap $
    elem
      (addIds elemName elemScope $ addStyle newStyle props)
  where
  oldStyle = toStyle someStyle
  styleMap /\ newStyle = getStyleMap elemName oldStyle

styleKeyedNode
  :: forall html style a
   . Html html
  => HtmlStyled html
  => IsStyle style
  => ElemKeyedNode html a
  -> style
  -> ElemKeyedNode html a
styleKeyedNode =
  styleKeyedNodeNamed Nothing Nothing

styleKeyedNodeNamed
  :: forall html style a
   . Html html
  => HtmlStyled html
  => IsStyle style
  => Maybe ElemName
  -> Maybe ElemScope
  -> ElemKeyedNode html a
  -> style
  -> ElemKeyedNode html a
styleKeyedNodeNamed elemName elemScope elem someStyle props children =
  registerStyleMap styleMap $
    elem
      (addIds elemName elemScope $ addStyle newStyle props)
      children
  where
  oldStyle = toStyle someStyle
  styleMap /\ newStyle = getStyleMap elemName oldStyle

styleKeyedLeaf
  :: forall html style a
   . Html html
  => HtmlStyled html
  => IsStyle style
  => ElemKeyedLeaf html a
  -> style
  -> ElemKeyedLeaf html a
styleKeyedLeaf = styleKeyedLeafNamed Nothing Nothing

styleKeyedLeafNamed
  :: forall html style a
   . Html html
  => HtmlStyled html
  => IsStyle style
  => Maybe ElemName
  -> Maybe ElemScope
  -> ElemKeyedLeaf html a
  -> style
  -> ElemKeyedLeaf html a
styleKeyedLeafNamed elemName elemScope elem someStyle props =
  registerStyleMap styleMap $
    elem
      (addIds elemName elemScope $ addStyle newStyle props)
  where
  oldStyle = toStyle someStyle
  styleMap /\ newStyle = getStyleMap elemName oldStyle

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

derive instance Newtype InlineStyle _

derive instance Newtype ClassName _

derive newtype instance Semigroup Style

derive newtype instance Monoid Style

derive newtype instance Hashable HashedAnimName
derive instance Eq HashedAnimName

derive newtype instance Hashable AnimDecl
derive instance Eq AnimDecl

derive newtype instance Hashable AnimStep
derive instance Eq AnimStep

derive newtype instance Hashable ClassName
derive instance Eq ClassName

derive newtype instance Hashable Selector
derive instance Eq Selector

derive newtype instance Hashable StyleDecl
derive newtype instance Semigroup StyleDecl
derive instance Eq StyleDecl

derive instance Newtype ElemName _
derive instance Eq ElemName

instance IsStyle Style where
  toStyle = identity

instance IsStyle String where
  toStyle str = mempty
    # \(Style rec) -> Style $ rec { declarations = [ decl str ] }

instance IsStyle Unit where
  toStyle _ = mempty

instance IsStyle (Array String) where
  toStyle xs = mempty
    # \(Style rec) -> Style $ rec
        { declarations =
            [ StyleDecl
                [ Nothing /\ map mergeDecl xs ]
            ]
        }

else instance IsStyle a => IsStyle (Array a) where
  toStyle xs = fold (toStyle <$> xs)

instance IsStyle ClassName where
  toStyle c = mempty
    # \(Style rec) -> Style $ rec { classes = [ c ] }

instance IsStyle a => IsStyle (Maybe a) where
  toStyle = case _ of
    Just x -> toStyle x
    Nothing -> mempty

instance IsStyle StyleDecl where
  toStyle c = mempty
    # \(Style rec) -> Style $ rec { declarations = [ c ] }

instance IsStyle Anim where
  toStyle anim' = mempty
    # \(Style rec) -> Style $ rec { animations = [ anim' ] }

instance (IsStyle a, IsStyle b) => IsStyle (a /\ b) where
  toStyle (s1 /\ s2) = toStyle s1 <> toStyle s2

class IsDecl a where
  mergeDecl :: a -> String

instance IsDecl String where
  mergeDecl str = str

instance IsDecl a => IsDecl (Array a) where
  mergeDecl xs = Str.joinWith ";" (mergeDecl <$> xs)

instance IsDecl Unit where
  mergeDecl _ = ""

-------------------------------------------------------------------------------
-- Utils
-------------------------------------------------------------------------------

inlineToProp :: forall a. Array InlineStyle -> Prop a
inlineToProp inlineStyles = VP.style (Str.joinWith ";" $ map unwrap inlineStyles)

classesToProp :: forall a. Array ClassName -> Prop a
classesToProp classes = VP.className (Str.joinWith " " $ unwrap <$> classes)

insertProp :: forall a. String -> (Maybe (Prop a) -> Prop a) -> Array (Prop a) -> Array (Prop a)
insertProp key fn props =
  if isJust $ Array.find isKey props then
    map (\x -> if isKey x then fn (Just x) else x) props
  else
    props <> [ fn Nothing ]
  where
  isKey = case _ of
    Attr key' _ -> key' == key
    Event key' _ -> key' == key

addStyle :: forall a. Style -> Array (Prop a) -> Array (Prop a)
addStyle style props =
  ( props
      # insertProp "style" mapStyle
      # insertProp "className" mapClassName
  )
  where
  Style { inline, classes } = toStyle style

  mapStyle = case _ of
    Just (Attr "style" s) -> inlineToProp (inline <> [ InlineStyle s ])
    _ -> inlineToProp inline

  mapClassName = case _ of
    Just (Attr "className" cs) -> classesToProp (classes <> [ ClassName cs ])
    _ -> classesToProp classes

addIds :: forall a. Maybe ElemName -> Maybe ElemScope -> Array (Prop a) -> Array (Prop a)
addIds elemName elemScope props =
  let
    elemName' = case elemName of
      Nothing -> []
      Just (ElemName name) ->
        [ C.attr "data-el" name ]

    elemScope' = case elemScope of
      Nothing -> []
      Just (ElemScope scope) | elemName == Just (ElemName "root") ->
        [ C.attr "data-scope" scope ]
      _ -> []

  in
    elemName' <> elemScope' <> props

replaceByMap :: HashMap String String -> String -> String
replaceByMap replaceMap str =
  HashMap.toArrayBy Tuple replaceMap
    # foldr (\(key /\ value) -> Str.replace (Pattern key) (Replacement value)) str