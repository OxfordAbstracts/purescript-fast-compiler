module Chameleon.Styled.Elems
  ( class StyleElems
  , styleElems
  , styleElems'
  , class StyleElemsRL
  , styleElemsRL
  , class StyleElemsOne
  , styleElemsOne
  ) where

import Prelude

import Chameleon (Key, Prop)
import Chameleon as C
import Chameleon.Styled.Core (class HtmlStyled, class IsStyle, ElemName(..), ElemScope(..), Style, styleKeyedNodeNamed, styleLeafNamed, styleNodeNamed, toStyle)
import Data.Maybe (Maybe(..))
import Data.Reflectable (class Reflectable, reflectType)
import Data.Symbol (class IsSymbol, reflectSymbol)
import Data.Tuple.Nested (type (/\), (/\))
import Prim.Int (class Add)
import Prim.Row as Row
import Prim.RowList (class RowToList, RowList)
import Prim.RowList as RL
import Prim.Symbol as Sym
import Prim.TypeError (class Warn, Text)
import Record as Record
import Type.Proxy (Proxy(..))

styleElems
  :: forall rowIn rowOut
   . StyleElems rowIn rowOut
  => String
  -> Record rowIn
  -> Record rowOut
styleElems elemScope =
  styleElems'
    elemScope
    (\_ _ -> mempty :: Style)

class
  StyleElems
    (rowIn :: Row Type)
    (rowOut :: Row Type)
  | rowIn -> rowOut
  where
  styleElems'
    :: forall style
     . IsStyle style
    => String
    -> (Int -> String -> style)
    -> Record rowIn
    -> Record rowOut

instance
  ( RowToList rowIn rowlist
  , StyleElemsRL 0 rowlist rowIn rowOut
  ) =>
  StyleElems rowIn rowOut
  where
  styleElems' elemScope mkExtraStyle = styleElemsRL
    (ElemScope elemScope)
    (\index (ElemName elemName') -> toStyle $ mkExtraStyle index elemName')
    (Proxy :: Proxy 0)
    (Proxy :: Proxy rowlist)

--------------------------------------------------------------------------------

class
  StyleElemsRL
    (index :: Int)
    (rowlist :: RowList Type)
    (rowIn :: Row Type)
    (rowOut :: Row Type)
  | rowlist rowIn index -> rowOut
  where
  styleElemsRL
    :: ElemScope
    -> (Int -> ElemName -> Style)
    -> Proxy index
    -> Proxy rowlist
    -> Record rowIn
    -> Record rowOut

instance StyleElemsRL index RL.Nil row () where
  styleElemsRL _ _ _ _ _ = {}

instance
  ( StyleElemsRL indexPrev rowlistPrev rowIn rowOutPrev
  , Row.Cons sym typ rowTrash rowIn
  , Row.Cons sym (Array (Prop a) -> styledElem_) rowOutPrev rowOutTmp
  , Row.Cons sym_ styledElem_ rowOutTmp rowOut
  , Sym.Append sym "_" sym_
  , Row.Lacks sym rowOutPrev
  , Row.Lacks sym_ rowOutTmp
  , StyleElemsOne typ (Array (Prop a) -> styledElem_)
  , IsSymbol sym
  , IsSymbol sym_
  , Add 1 indexPrev index
  , Reflectable index Int
  ) =>
  StyleElemsRL
    index
    (RL.Cons sym typ rowlistPrev)
    rowIn
    rowOut
  where
  styleElemsRL
    :: ElemScope
    -> (Int -> ElemName -> Style)
    -> Proxy index
    -> Proxy (RL.Cons sym typ rowlistPrev)
    -> Record rowIn
    -> Record rowOut
  styleElemsRL elemScope mkExtraStyle _ _ recordIn =
    let
      recordPrev :: Record rowOutPrev
      recordPrev = styleElemsRL
        elemScope
        mkExtraStyle
        (Proxy :: Proxy indexPrev)
        (Proxy :: Proxy rowlistPrev)
        recordIn

      spec :: typ
      spec = Record.get proxySym recordIn

      elemName :: ElemName
      elemName = ElemName (reflectSymbol proxySym)

      index :: Int
      index = reflectType proxyIndex

      extraStyle :: Style
      extraStyle = mkExtraStyle index elemName

      styledElem :: Array (Prop a) -> styledElem_
      styledElem = styleElemsOne elemName elemScope extraStyle spec

      styledElem_ :: styledElem_
      styledElem_ = styledElem []

      proxySym :: Proxy sym
      proxySym = Proxy

      proxySym_ :: Proxy sym_
      proxySym_ = Proxy

      proxyIndex :: Proxy index
      proxyIndex = Proxy
    in
      recordPrev
        # Record.insert proxySym styledElem
        # Record.insert proxySym_ styledElem_

--------------------------------------------------------------------------------

class
  StyleElemsOne
    (typ :: Type)
    (styledElem :: Type)
  | typ -> styledElem
  where
  styleElemsOne :: ElemName -> ElemScope -> Style -> typ -> styledElem

instance leaf ::
  ( HtmlStyled html
  ) =>
  StyleElemsOne
    (Array (Prop a) -> html a)
    (Array (Prop a) -> html a)
  where
  styleElemsOne elemName elemScope extraStyle elem =
    styleLeafNamed (Just elemName) (Just elemScope) elem extraStyle

else instance node ::
  ( HtmlStyled html
  ) =>
  StyleElemsOne
    (Array (Prop a) -> Array (html a) -> html a)
    (Array (Prop a) -> Array (html a) -> html a)
  where
  styleElemsOne elemName elemScope extraStyle elem =
    styleNodeNamed (Just elemName) (Just elemScope) elem extraStyle

else instance keyedNode ::
  ( HtmlStyled html
  ) =>
  StyleElemsOne
    (Array (Prop a) -> Array (Key /\ html a) -> html a)
    (Array (Prop a) -> Array (Key /\ html a) -> html a)
  where
  styleElemsOne elemName elemScope extraStyle elem =
    styleKeyedNodeNamed (Just elemName) (Just elemScope) elem extraStyle

else instance leafStyled ::
  ( IsStyle style
  , HtmlStyled html
  ) =>
  StyleElemsOne
    ((Array (Prop a) -> html a) /\ style)
    (Array (Prop a) -> html a)
  where
  styleElemsOne elemName elemScope extraStyle (elem /\ style) =
    styleLeafNamed
      (Just elemName)
      (Just elemScope)
      elem
      (toStyle style <> extraStyle)

else instance leafStyledOpt ::
  ( IsStyle style
  , HtmlStyled html
  ) =>
  StyleElemsOne
    (Record opt -> (Array (Prop a) -> html a) /\ style)
    (Record opt -> Array (Prop a) -> html a)
  where
  styleElemsOne elemName elemScope extraStyle f opt =
    let
      elem /\ style = f opt
    in
      styleLeafNamed
        (Just elemName)
        (Just elemScope)
        elem
        (toStyle style <> extraStyle)

else instance nodeStyled ::
  ( IsStyle style
  , HtmlStyled html
  ) =>
  StyleElemsOne
    ((Array (Prop a) -> Array (html a) -> html a) /\ style)
    (Array (Prop a) -> Array (html a) -> html a)
  where
  styleElemsOne elemName elemScope extraStyle (elem /\ style) =
    styleNodeNamed
      (Just elemName)
      (Just elemScope)
      elem
      (toStyle style <> extraStyle)

else instance nodeStyledOpt ::
  ( IsStyle style
  , HtmlStyled html
  ) =>
  StyleElemsOne
    (Record opt -> (Array (Prop a) -> Array (html a) -> html a) /\ style)
    (Record opt -> Array (Prop a) -> Array (html a) -> html a)
  where
  styleElemsOne elemName elemScope extraStyle f opt =
    let
      elem /\ style = f opt
    in
      styleNodeNamed
        (Just elemName)
        (Just elemScope)
        elem
        (toStyle style <> extraStyle)

else instance keyedNodeStyledOpt ::
  ( IsStyle style
  , HtmlStyled html
  ) =>
  StyleElemsOne
    (Record opt -> (Array (Prop a) -> Array (Key /\ html a) -> html a) /\ style)
    (Record opt -> Array (Prop a) -> Array (Key /\ html a) -> html a)
  where
  styleElemsOne elemName elemScope extraStyle f opt =
    let
      elem /\ style = f opt
    in
      styleKeyedNodeNamed
        (Just elemName)
        (Just elemScope)
        elem
        (toStyle style <> extraStyle)

else instance onlyStyle ::
  ( IsStyle style
  , HtmlStyled html
  , Warn (Text "implicit div")
  ) =>
  StyleElemsOne
    (style)
    (Array (Prop a) -> Array (html a) -> html a)
  where
  styleElemsOne elemName elemScope extraStyle style =
    styleNodeNamed
      (Just elemName)
      (Just elemScope)
      C.div
      (toStyle style <> extraStyle)

