module Data.Text.Format.Org.Types where

import Prelude

import Foreign (Foreign, F)
import Prim.RowList as RL

import Type.Proxy (Proxy(..))

import Data.Maybe (Maybe(..), fromMaybe)
import Data.Array as Array
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NEA
import Data.String (CodePoint)
import Data.String (length) as String
import Data.Map (Map)
import Data.Map as Map
import Data.Date (Date, Weekday, canonicalDate)
import Data.Date (day, month, year) as D
import Data.Tuple as Tuple
import Data.Time (Time(..))
import Data.Time as Time
import Data.Enum (fromEnum, toEnum)
import Data.Either (Either(..))
-- import Data.Time (TimeOfDay)
import Data.Variant (Variant)
import Data.Variant (match) as Variant
import Data.Tuple.Nested ((/\), type (/\))
import Data.String.CodePoints (codePointFromChar)
import Data.Newtype (class Newtype, wrap, unwrap)
import Data.Bifunctor (lmap, bimap)

import Yoga.JSON (class ReadForeign, class WriteForeign, class ReadForeignFields, class WriteForeignFields, class ReadForeignVariant, class WriteForeignVariant, readImpl, writeImpl, writeJSON)
import Yoga.Json.Extra (Case, Case1, Case2, Case3, Case4, readMatchImpl)
import Yoga.Json.Extra
    ( use, use1, use2, use3, use4
    , select, select1, select2, select3, select4, todo
    , uncase, uncase1, uncase2, uncase3, uncase4
    ) as Variant

import Data.Text.Format.Org.Keyword (OrgKeywords, OrgKeyword, JsonKeywords(..), JsonKeywordRow, JsonKeywordOrPropRec)
import Data.Text.Format.Org.Keyword (empty, toRec, fromRec, fromJson, toJson) as KW
import Data.Text.Format.Org.Property (OrgProperties, OrgProperty, JsonProperties, JsonPropertyRow)
import Data.Text.Format.Org.Property (empty, toRec, fromRec, fromJson, toJson) as Prop

-- inspired by https://hackage.haskell.org/package/org-mode-2.1.0/docs/Data-Org.html


data OrgFile =
    OrgFile
        { meta  :: OrgKeywords String
        , props :: OrgProperties String -- could be part of the top section?
        , doc :: OrgDoc
        }


newtype OrgDoc =
    OrgDoc
        { zeroth :: Array Block
        , sections :: Array Section
        }


data Block
    = Of BlockKind (NonEmptyArray Words)
    | IsDrawer Drawer -- FIXME: drawers can contain anything, so another blocks as well, but as `WithKeyword` it causes recursion when converting to JSON
    -- | Centered (NonEmptyArray Words) -- TODO
    | Footnote String (NonEmptyArray Words)
    | List ListItems
    | DetachedItem DetachedListItem -- used only for `EBNF` parsing
    | Table (Maybe TableFormat) (NonEmptyArray TableRow)
    | Paragraph (NonEmptyArray Words)
    | WithKeyword (OrgKeyword String) Block -- TODO: rename 'Affilated': https://orgmode.org/worg/dev/org-syntax-edited.html#Keywords
    | HRule
    | LComment (Array String)
    | FixedWidth (NonEmptyArray Words)
    | ClockB { start :: OrgDateTime, end :: Maybe OrgDateTime } Clock -- FIXME: use OrgDateTimeRange
    | JoinB Block Block


data Words
    = Marked MarkupKey String
    | Link LinkTarget (Maybe String)
    | RawLink LinkTarget -- link with no wrapping
    | Image ImageSource
    | RawImage ImageSource -- image with no wrapping
    | Punct CodePoint
    | Plain String
    | Markup String
    | DateTime { start :: OrgDateTime, end :: Maybe OrgDateTime }
    | ClockW Clock
    | DiaryW Diary
    | FootnoteRef { label :: String, def :: Maybe String } -- FIXME: support using `Words` here may be, but it causes recursion fails when exporting to JSON
    | Break
    | Entity String
    -- | Space
    -- | Indent Int
    | JoinW Words Words
    | EmptyW -- a stub for having `NonEmptyArray` at places, TODO: may be we could either get rid of it or don't require NEA at all


data BlockKind
    = Quote
    | Example
    | Center
    | Verse
    | Export
    | Comment
    | Code (Maybe Language) -- TODO: separate, because doesn't support words
    | Custom String (Array String)


data InlineKey
    = IComment
    | IHtml


data MarkupKey
    = Bold
    | Italic
    | Highlight
    | Underline
    | Verbatim
    | InlineCode
    | Inline InlineKey
    | Strike
    | Error
    | Subscript
    | Superscript
    | And MarkupKey MarkupKey


newtype OrgDateTime =
    OrgDateTime
        { date :: Date
        , time :: Maybe OrgTimeRange
        , repeat :: Maybe Repeater
        , delay :: Maybe Delay
        , active :: Boolean
        }


newtype OrgTimeRange =
    OrgTimeRange
        { start :: Time
        , end :: Maybe Time
        }


newtype OrgDateRange =
    OrgDateRange
        { start :: OrgDateTime
        , end :: Maybe OrgDateTime
        }


newtype Repeater =
    Repeater
        { mode :: RepeaterMode
        , value :: Int
        , interval :: Interval
        , with ::
            Maybe
                { value :: Int
                , interval :: Interval
                }
        }


data RepeaterMode
    = Single
    | FromToday
    | Jump


data Interval = Hour | Day | Week | Month | Year


newtype Delay =
    Delay
        { mode :: DelayMode
        , value :: Int
        , interval :: Interval
        }


data DelayMode
    = One
    | All


newtype Drawer =
    Drawer
        { name :: String
        , content :: NonEmptyArray Words
        }


newtype Planning =
    Planning
        { closed :: Maybe OrgDateTime
        , deadline :: Maybe OrgDateTime
        , scheduled :: Maybe OrgDateTime
        , timestamp :: Maybe OrgDateTime
        }


newtype Section =
    Section
        { todo :: Maybe Todo
        , priority :: Maybe Priority
        , cookie :: Maybe Cookie
        , check :: Maybe Check -- TODO:  shouldn't be in section?
        , heading :: NonEmptyArray Words
        , level :: Int
        , tags :: Array String
        , planning :: Planning
        , props :: OrgProperties String
        , logbook :: Maybe LogBook
        , drawers :: Array Drawer
        , comment :: Boolean
        , doc :: OrgDoc
        }


newtype Clock =
    Clock -- FIXME: inactive timestamp + duration
        { hour :: Int
        , minute :: Int
        , second :: Maybe Int
        }


newtype Diary =
    Diary
        { expr :: String
        , time :: Maybe OrgTimeRange
        }


data LogBookEntrySubject
    = StateChange Todo Todo OrgDateTime
    | Reschedule OrgDateTime OrgDateTime
    | NoteTaken OrgDateTime
    | Other (Array Words) (Array OrgDateTime)


newtype LogBookEntry
    = LogBookEntry
        { subject :: LogBookEntrySubject
        , continuation :: Array (Array Words)
        }


newtype LogBook = LogBook (Array LogBookEntry)


data Todo
    = Todo
    | Doing
    | Done
    | Now
    | Next
    | CustomKW String


data Priority
    = Alpha Char
    | Num Int


data Cookie
    = Split
    | Percent
    | Pie


data Check
    = Check
    | Uncheck
    | Halfcheck


data Counter
    = Counter Int


data ListType
    = Bulleted
    | Plussed
    | Numbered
    | NumberedFrom Int
    | Hyphened
    | Alphed
    | Prefixed String


derive instance Eq ListType


newtype TableFormat = TableFormat String
newtype TableCustomBreak = TableCustomBreak String


data TableRow = BreakT (Maybe TableCustomBreak) | Row (NonEmptyArray TableColumn)


data TableColumn = Empty | Column (NonEmptyArray Words)


data ListItems = ListItems ListType (NonEmptyArray Item)


data DetachedListItem =
    DetachedListItem
        ListType
        { mbIndent :: Maybe String -- having it set overrides the natural indent / TODO: make out indent possible to override
        }
        ListItemProps
        (NonEmptyArray Words)


type ListItemProps =
    { check :: Maybe Check
    , counter :: Maybe Counter
    , tag :: Maybe String
    , drawers :: Array Drawer
    }


data Item =
    Item
        ListItemProps
        (NonEmptyArray Words)
        (Maybe ListItems)


data LinkTarget
    = Remote String
    | Local String
    | Heading String


data ImageSource
    = RemoteSrc String
    | LocalSrc String


newtype Language = Language String


{- ----- Newtype ------- -}

derive instance Newtype Language _
derive instance Newtype Drawer _
derive instance Newtype OrgDateTime _
derive instance Newtype OrgTimeRange _
derive instance Newtype Repeater _
derive instance Newtype Delay _
derive instance Newtype Planning _
derive instance Newtype Clock _
derive instance Newtype Diary _
derive instance Newtype LogBookEntry _
derive instance Newtype LogBook _
derive instance Newtype TableFormat _
derive instance Newtype TableCustomBreak _

-- internals below, they don't need Newtype instance

-- derive instance Newtype Section _
-- derive instance Newtype OrgDoc _
-- derive instance Newtype OrgFile _

{- ----- Show & Eq ----- -}


instance Show Check where
    show = case _ of
        Check -> "check"
        Uncheck -> "un-check"
        Halfcheck -> "half-check"

derive instance Eq Check


{- ----- JSON ----- -}


class JsonOverRow (row :: Row Type) a | a -> row where
    convert :: a -> Record row
    load :: Record row -> a


class JsonOverRow row a <= JsonOverRowH (row :: Row Type) a | a -> row where
    readImplRow :: Foreign -> F a
    writeImplRow :: a -> Foreign


class JsonOverVariant (row :: Row Type) a | a -> row where
    readForeign :: Foreign -> F a
    toVariant :: a -> Variant row
    fromVariant :: Variant row -> a -- TODO: could be used / joined with `readForeign`, or `readForeign` could use `fromVariant` as binding


class JsonOverVariant row a <= JsonOverVariantH (row :: Row Type) a | a -> row where
    readImplVar :: Foreign -> F a
    writeImplVar :: a -> Foreign


class Newtype a x <= JsonOverNewtype a x | a -> x, x -> a where -- FIXME: not used?
    readImplNT :: Foreign -> F a
    writeImplNT :: a -> Foreign


instance (RL.RowToList row rl, ReadForeignVariant rl row, WriteForeignVariant rl row, JsonOverVariant row a) => JsonOverVariantH row a where
    readImplVar = readForeign
    writeImplVar = writeImpl <<< toVariant


instance (ReadForeign x, WriteForeign x, Newtype a x) => JsonOverNewtype a x where
    readImplNT f = (readImpl f :: F x) <#> wrap
    writeImplNT = unwrap >>> writeImpl


instance
    ( RL.RowToList row rl
    , ReadForeignFields rl () row
    , WriteForeignFields rl row () to
    , JsonOverRow row a
    ) => JsonOverRowH row a where
    readImplRow f = (readImpl f :: F (Record row)) <#> load
    writeImplRow = convert >>> writeImpl


-- instance (ReadForeign x, JsonOverNewtype a x) => ReadForeign a where
--     readImpl f = (readImpl f :: F x) <#> wrap


type CheckRow =
    ( check :: Case
    , uncheck :: Case
    , halfcheck :: Case
    )


readCheck :: Foreign -> F Check
readCheck =
    readMatchImpl
        (Proxy :: _ CheckRow)
        { check : Variant.use Check
        , uncheck : Variant.use Uncheck
        , halfcheck : Variant.use Halfcheck
        }


checkToVariant :: Check -> Variant CheckRow
checkToVariant = case _ of
    Check -> Variant.select (Proxy :: _ "check")
    Uncheck -> Variant.select (Proxy :: _ "uncheck")
    Halfcheck -> Variant.select (Proxy :: _ "halfcheck")



checkFromVariant :: Variant CheckRow -> Check
checkFromVariant =
    Variant.match
        { check : Variant.uncase Check
        , uncheck : Variant.uncase Uncheck
        , halfcheck : Variant.uncase Halfcheck
        }


instance ReadForeign Check where readImpl = readImplVar
instance WriteForeign Check where writeImpl = writeImplVar
instance JsonOverVariant CheckRow Check where
    readForeign = readCheck
    toVariant = checkToVariant
    fromVariant = checkFromVariant


instance ReadForeign Language where readImpl = readImplNT
instance WriteForeign Language where writeImpl = writeImplNT


type LinkTargetRow =
    ( remote :: Case1 String
    , local :: Case1 String
    , heading :: Case1 String
    )


readLinkTarget :: Foreign -> F LinkTarget
readLinkTarget =
    readMatchImpl
        (Proxy :: _ LinkTargetRow)
        { remote : Variant.use1 Remote
        , local : Variant.use1 Local
        , heading : Variant.use1 Heading
        }


linkTargetToVariant :: LinkTarget -> Variant LinkTargetRow
linkTargetToVariant = case _ of
    Remote url  -> Variant.select1 (Proxy :: _ "remote") url
    Local url   -> Variant.select1 (Proxy :: _ "local") url
    Heading trg -> Variant.select1 (Proxy :: _ "heading") trg



linkTargetFromVariant :: Variant LinkTargetRow -> LinkTarget
linkTargetFromVariant =
    Variant.match
        { remote : Variant.uncase1 >>> Remote
        , local : Variant.uncase1 >>> Local
        , heading : Variant.uncase1 >>> Heading
        }


instance ReadForeign LinkTarget where readImpl = readImplVar
instance WriteForeign LinkTarget where writeImpl = writeImplVar
instance JsonOverVariant LinkTargetRow LinkTarget where
    readForeign = readLinkTarget
    toVariant = linkTargetToVariant
    fromVariant = linkTargetFromVariant


type ImageSourceRow =
    ( remote :: Case1 String
    , local :: Case1 String
    )


readImageSource :: Foreign -> F ImageSource
readImageSource =
    readMatchImpl
        (Proxy :: _ ImageSourceRow)
        { remote : Variant.use1 RemoteSrc
        , local : Variant.use1 LocalSrc
        }


imageSourceToVariant :: ImageSource -> Variant ImageSourceRow
imageSourceToVariant = case _ of
    RemoteSrc url -> Variant.select1 (Proxy :: _ "remote") url
    LocalSrc url  -> Variant.select1 (Proxy :: _ "local") url


imageSourceFromVariant :: Variant ImageSourceRow -> ImageSource
imageSourceFromVariant =
    Variant.match
        { remote : Variant.uncase1 >>> RemoteSrc
        , local : Variant.uncase1 >>> LocalSrc
        }


instance ReadForeign ImageSource where readImpl = readImplVar
instance WriteForeign ImageSource where writeImpl = writeImplVar
instance JsonOverVariant ImageSourceRow ImageSource where
    readForeign = readImageSource
    toVariant = imageSourceToVariant
    fromVariant = imageSourceFromVariant


emptyItem :: Item
emptyItem =
    Item
        { check : Nothing
        , counter : Nothing
        , tag : Nothing
        , drawers : []
        }
        (importWords [])
        Nothing


emptyDetItem :: DetachedListItem
emptyDetItem = detachedFromItem Bulleted emptyItem


type JsonListItemsRow =
    ( type_ :: Variant ListTypeRow
    , values :: Array JsonListItem
    )


convertListItems :: ListItems -> Record JsonListItemsRow
convertListItems (ListItems itemType children) =
    { type_ : toVariant itemType
    , values : NEA.toArray $ convertListItem <$> children
    }


loadListItems :: Record JsonListItemsRow -> ListItems
loadListItems rec =
    ListItems
        (fromVariant rec.type_)
        $ toNEA emptyItem $ loadListItem <$> rec.values


instance ReadForeign ListItems where readImpl = readImplRow
instance WriteForeign ListItems where writeImpl = writeImplRow
instance JsonOverRow JsonListItemsRow ListItems where
    convert = convertListItems
    load = loadListItems


type JsonListItemRow =
    ( words :: Array Words
    , tag :: Maybe String
    , check :: Maybe (Variant CheckRow)
    , counter :: Maybe Int
    , children :: Maybe (Record JsonListItemsRow)
    , drawers :: Array Drawer
    )


newtype JsonListItem =
    JsonListItem (Record JsonListItemRow)


convertListItem :: Item -> JsonListItem
convertListItem  (Item def ws mbChildren) =
    JsonListItem
        { words : exportWords ws
        , tag : def.tag
        , check : toVariant <$> def.check
        , counter : (\(Counter n) -> n) <$> def.counter
        , children : convertListItems <$> mbChildren
        , drawers : def.drawers
        }


loadListItem :: JsonListItem -> Item
loadListItem (JsonListItem item) =
    Item
        { check : fromVariant <$> item.check
        , counter : Counter <$> item.counter
        , tag : item.tag
        , drawers : item.drawers
        }
        (importWords $ item.words)
        $ loadListItems <$> item.children


itemFromDetached :: DetachedListItem -> Item
itemFromDetached (DetachedListItem _ _ props words) =
    Item props words Nothing


detachedFromItem :: ListType -> Item -> DetachedListItem
detachedFromItem ltype (Item props words _) =
    DetachedListItem
        ltype
        { mbIndent : Nothing }
        props
        words


convertDetachedItem :: DetachedListItem -> JsonListItem
convertDetachedItem = itemFromDetached >>> convertListItem


loadDetachedItem :: ListType -> JsonListItem -> DetachedListItem
loadDetachedItem ltype = loadListItem >>> detachedFromItem ltype


setIndent :: { indent :: String } -> DetachedListItem -> DetachedListItem
setIndent { indent } (DetachedListItem ltype _ props words) =
    DetachedListItem
        ltype
        { mbIndent : if String.length indent > 0 then Just indent else Nothing }
        props
        words


type BlockKindRow =
    ( quote :: Case
    , example :: Case
    , center :: Case
    , verse :: Case
    , export :: Case
    , comment :: Case
    , code :: Case1 (Maybe Language)
    , custom :: Case2 String (Array String)
    )


readBlockKind :: Foreign -> F BlockKind
readBlockKind =
    readMatchImpl
        (Proxy :: _ BlockKindRow)
        { quote : Variant.use Quote
        , example : Variant.use Example
        , center : Variant.use Center
        , verse : Variant.use Verse
        , export : Variant.use Export
        , comment : Variant.use Comment
        , code : Variant.use1 Code
        , custom : Variant.use2 Custom
        }


blockKindToVariant :: BlockKind -> Variant BlockKindRow
blockKindToVariant = case _ of
    Quote -> Variant.select (Proxy :: _ "quote")
    Example -> Variant.select (Proxy :: _ "example")
    Center -> Variant.select (Proxy :: _ "center")
    Verse -> Variant.select (Proxy :: _ "verse")
    Export -> Variant.select (Proxy :: _ "export")
    Comment -> Variant.select (Proxy :: _ "comment")
    Code mbLang -> Variant.select1 (Proxy :: _ "code") mbLang
    Custom name args -> Variant.select2 (Proxy :: _ "custom") name args


blockKindFromVariant :: Variant BlockKindRow -> BlockKind
blockKindFromVariant =
    Variant.match
        { quote : Variant.uncase Quote
        , example : Variant.uncase Example
        , center : Variant.uncase Center
        , verse : Variant.uncase Verse
        , export : Variant.uncase Export
        , comment : Variant.uncase Comment
        , code : Variant.uncase1 >>> Code
        , custom : Variant.uncase2 >>> Tuple.uncurry Custom
        }


instance ReadForeign BlockKind where readImpl = readImplVar
instance WriteForeign BlockKind where writeImpl = writeImplVar
instance JsonOverVariant BlockKindRow BlockKind where
    readForeign = readBlockKind
    toVariant = blockKindToVariant
    fromVariant = blockKindFromVariant


type BlockRow =
    ( kind :: Case2 BlockKind (Array Words)
    , drawer :: Case2 String (Array Words)
    , paragraph :: Case1 (Array Words)
    , footnote :: Case2 String (Array Words)
    , hr :: Case
    , fixed :: Case1 (Array Words)
    , comment :: Case1 (Array String)
    , list :: Case2 (Variant ListTypeRow) (Array JsonListItem)
    , litem :: Case3 (Variant ListTypeRow) { indent :: String } JsonListItem
    , table :: Case1 { format :: Maybe String, rows :: JsonRows }
    , clock :: Case3 (Record JsonDateTimeRow) (Maybe (Record JsonDateTimeRow)) (Record ClockRow)
    )


instance ReadForeign JsonListItem where readImpl f = (readImpl f :: F (Record JsonListItemRow)) <#> JsonListItem
instance WriteForeign JsonListItem where writeImpl (JsonListItem items) = writeImpl items


toNEA :: forall a. a -> Array a -> NonEmptyArray a
toNEA a = NEA.fromArray >>> fromMaybe (NEA.singleton a)


importWords :: Array Words -> NonEmptyArray Words
importWords = toNEA $ EmptyW -- FIXME: use some default `Words`
exportWords :: NonEmptyArray Words -> Array Words
exportWords = NEA.toArray >>> flattenWords


importItems :: Array JsonListItem -> NonEmptyArray Item
importItems = map loadListItem >>> toNEA emptyItem
exportItems :: NonEmptyArray Item -> Array JsonListItem
exportItems = NEA.toArray >>> map convertListItem


type JsonRows = Array (Either String (Array (Array Words)))


importRows :: JsonRows -> NonEmptyArray TableRow
importRows =
    map importRow >>> toNEA (BreakT Nothing)
    where
        importColumn [] = Empty
        importColumn ws = Column $ importWords ws
        importRow (Right []) = BreakT Nothing -- FIXME: breaks are imported as columns
        importRow (Right columns) = Row $ toNEA Empty $ importColumn <$> columns
        importRow (Left break) = BreakT $ Just $ TableCustomBreak break
exportRows :: NonEmptyArray TableRow -> JsonRows
exportRows =
    NEA.toArray >>> map exportRow
    where
        exportColumn Empty = []
        exportColumn (Column ws) = exportWords ws
        exportRow (BreakT (Just customBreak)) = Left $ unwrap customBreak
        exportRow (BreakT Nothing) = Right []
        exportRow (Row columns) = Right $ exportColumn <$> NEA.toArray columns


readBlock :: Foreign -> F Block
readBlock =
    readMatchImpl
        (Proxy :: _ BlockRow)
        { kind : Variant.use2 $ \kind ws -> Of kind $ importWords ws
        , drawer : Variant.use2 $ \name ws -> IsDrawer $ Drawer { name, content : importWords ws }
        , footnote : Variant.use2 $ \label ws -> Footnote label $ importWords ws
        , paragraph : Variant.use1 $ Paragraph <<< importWords
        , hr : Variant.use HRule
        , fixed : Variant.use1 $ FixedWidth <<< importWords
        , comment : Variant.use1 LComment
        , list : Variant.use2 $ \ltype items -> List $ ListItems (fromVariant ltype) $ importItems items
        , litem : Variant.use3 $ \ltype { indent } itemdef ->
                        DetachedItem $ setIndent { indent } $ loadDetachedItem (fromVariant ltype) itemdef
        , table : Variant.use1 $ \{ format, rows } -> Table (wrap <$> format) $ importRows rows
        , clock : Variant.use3 $ \start end clock ->
                        ClockB { start : load start, end : load <$> end } $ wrap clock
        }


blockToVariant :: Block -> Variant BlockRow
blockToVariant = case _ of
    Of kind words -> Variant.select2 (Proxy :: _ "kind") kind $ exportWords words
    Paragraph words -> Variant.select1 (Proxy :: _ "paragraph") $ exportWords words
    IsDrawer (Drawer { name, content }) -> Variant.select2 (Proxy :: _ "drawer") name $ exportWords content
    Footnote label words -> Variant.select2 (Proxy :: _ "footnote") label $ exportWords words
    HRule -> Variant.select (Proxy :: _ "hr")
    FixedWidth words -> Variant.select1 (Proxy :: _ "fixed") $ exportWords words
    LComment lines -> Variant.select1 (Proxy :: _ "comment") lines
    WithKeyword _ _ -> Variant.select2 (Proxy :: _ "kind") Quote [ Plain "ERR" ] -- Keywords are handled on top level
    List (ListItems listType items) -> Variant.select2 (Proxy :: _ "list") (toVariant listType) $ exportItems items
    DetachedItem ditem@(DetachedListItem ltype { mbIndent } _ _) ->
        Variant.select3 (Proxy :: _ "litem")
            (toVariant ltype)
            { indent : fromMaybe "" mbIndent }
            $ convertDetachedItem ditem
    Table mbFormat rows -> Variant.select1 (Proxy :: _ "table") { format : unwrap <$> mbFormat, rows : exportRows rows }
    ClockB { start, end } clock ->
        Variant.select3 (Proxy :: _ "clock") (convert start) (convert <$> end) $ unwrap clock
    JoinB _ _ -> Variant.select2 (Proxy :: _ "kind") Quote [ Plain "ERR" ] -- Joins are handled on top level


blockFromVariant :: Variant BlockRow -> Block
blockFromVariant =
    Variant.match
        { kind : Variant.uncase2 >>> Tuple.uncurry \kind content -> Of kind $ importWords content
        , hr : Variant.uncase HRule
        , fixed : Variant.uncase1 >>> importWords >>> FixedWidth
        , paragraph : Variant.uncase1 >>> importWords >>> Paragraph
        , drawer : Variant.uncase2 >>> map importWords >>> Tuple.uncurry \name content -> IsDrawer $ Drawer { name, content }
        , footnote : Variant.uncase2 >>> map importWords >>> Tuple.uncurry Footnote
        , comment : Variant.uncase1 >>> LComment
        , list : Variant.uncase2 >>> Tuple.uncurry \ltype items -> List $ ListItems (fromVariant ltype) $ importItems items
        , litem : Variant.uncase3 >>> \(ltype /\ { indent } /\ def) ->
                        DetachedItem $ setIndent { indent } $ loadDetachedItem (fromVariant ltype) def
        , table : Variant.uncase1 >>> \{ format, rows } -> Table (wrap <$> format) $ importRows rows
        , clock : Variant.uncase3 >>> \(start /\ end /\ clock) ->
                        ClockB { start : load start, end : load <$> end } $ wrap clock
        }


instance ReadForeign Block where readImpl = readImplVar
instance WriteForeign Block where writeImpl = writeImplVar
instance JsonOverVariant BlockRow Block where
    readForeign = readBlock
    toVariant = blockToVariant
    fromVariant = blockFromVariant


type InlineKeyRow =
    ( comment :: Case
    , html :: Case
    )


readInlineKey :: Foreign -> F InlineKey
readInlineKey =
    readMatchImpl
        (Proxy :: _ InlineKeyRow)
        { comment : Variant.use IComment
        , html : Variant.use IHtml
        }


inlineKeyToVariant :: InlineKey -> Variant InlineKeyRow
inlineKeyToVariant = case _ of
    IComment -> Variant.select (Proxy :: _ "comment")
    IHtml -> Variant.select (Proxy :: _ "html")


inlineKeyFromVariant :: Variant InlineKeyRow -> InlineKey
inlineKeyFromVariant =
    Variant.match
        { comment : Variant.uncase IComment
        , html : Variant.uncase IHtml
        }


instance ReadForeign InlineKey where readImpl = readImplVar
instance WriteForeign InlineKey where writeImpl = writeImplVar
instance JsonOverVariant InlineKeyRow InlineKey where
    readForeign = readInlineKey
    toVariant = inlineKeyToVariant
    fromVariant = inlineKeyFromVariant


type MarkupKeyRow =
    ( bold :: Case
    , italic :: Case
    , highlight :: Case
    , underline :: Case
    , verbatim :: Case
    , inlineCode :: Case
    , inline :: Case1 InlineKey
    , strike :: Case
    , error :: Case
    , subscript :: Case
    , superscript :: Case
    )


readMarkupKey :: Foreign -> F MarkupKey
readMarkupKey =
    readMatchImpl
        (Proxy :: _ MarkupKeyRow)
        { bold : Variant.use Bold
        , italic : Variant.use Italic
        , highlight : Variant.use Highlight
        , underline : Variant.use Underline
        , verbatim : Variant.use Verbatim
        , inlineCode : Variant.use InlineCode
        , inline : Variant.use1 Inline
        , strike : Variant.use Strike
        , error : Variant.use Error -- FIXME
        , subscript : Variant.use Subscript -- FIXME
        , superscript : Variant.use Superscript -- FIXME
        }


markupKeyToVariant :: MarkupKey -> Variant MarkupKeyRow
markupKeyToVariant = case _ of
    Bold -> Variant.select (Proxy :: _ "bold")
    Italic -> Variant.select (Proxy :: _ "italic")
    Highlight -> Variant.select (Proxy :: _ "highlight")
    Underline -> Variant.select (Proxy :: _ "underline")
    Verbatim -> Variant.select (Proxy :: _ "verbatim")
    InlineCode -> Variant.select (Proxy :: _ "inlineCode")
    Inline key -> Variant.select1 (Proxy :: _ "inline") key
    Strike -> Variant.select (Proxy :: _ "strike")
    Error -> Variant.select (Proxy :: _ "error")
    Subscript -> Variant.select (Proxy :: _ "subscript")
    Superscript -> Variant.select (Proxy :: _ "superscript")
    And _ _ -> Variant.select (Proxy :: _ "error") -- we do not encode `And`, we unwrap it in a list of other keys


markupKeyFromVariant :: Variant MarkupKeyRow -> MarkupKey
markupKeyFromVariant =
    Variant.match
        { bold : Variant.uncase Bold
        , italic : Variant.uncase Italic
        , highlight : Variant.uncase Highlight
        , underline : Variant.uncase Underline
        , verbatim : Variant.uncase Verbatim
        , inlineCode : Variant.uncase InlineCode
        , inline : Variant.uncase1 >>> Inline
        , strike : Variant.uncase Strike
        , error : Variant.uncase Error -- FIXME
        , subscript : Variant.uncase Subscript
        , superscript : Variant.uncase Superscript
        }


markupKeyToRowArray :: MarkupKey -> Array (Variant MarkupKeyRow)
markupKeyToRowArray = case _ of
    And keyA keyB -> markupKeyToRowArray keyA <> markupKeyToRowArray keyB
    key -> Array.singleton $ markupKeyToVariant key


rowArrayToMarkupKey :: Array (Variant MarkupKeyRow) -> MarkupKey
rowArrayToMarkupKey vars =
    case NEA.fromArray vars of
        Just nea -> nea <#> fromVariant # NEA.foldl1 And
        Nothing -> Error



instance ReadForeign MarkupKey where readImpl = readImplVar
instance WriteForeign MarkupKey where writeImpl = writeImplVar
instance JsonOverVariant MarkupKeyRow MarkupKey where
    readForeign = readMarkupKey
    toVariant = markupKeyToVariant
    fromVariant = markupKeyFromVariant


type ClockRow =
    ( hour :: Int
    , minute :: Int
    , second :: Maybe Int
    )


instance ReadForeign Clock where readImpl = readImplNT
instance WriteForeign Clock where writeImpl = writeImplNT


type DiaryRow =
    ( expr :: String
    , time :: Maybe (Record JsonTimeRangeRow)
    )


convertDiary :: Diary -> Record DiaryRow
convertDiary = unwrap >>>
    case _ of
        { expr, time } ->
            { expr
            , time : convert <$> time
            }


loadDiary :: Record DiaryRow -> Diary
loadDiary =
    case _ of
        { expr, time } ->
            wrap
                { expr
                , time : load <$> time
                }


instance ReadForeign Diary where readImpl = readImplRow
instance WriteForeign Diary where writeImpl = writeImplRow
instance JsonOverRow DiaryRow Diary where
    convert = convertDiary
    load = loadDiary


type WordsRow =
    ( link :: Case2 LinkTarget (Maybe String)
    , linkRaw :: Case1 LinkTarget
    , image :: Case1 ImageSource
    , imageRaw :: Case1 ImageSource
    , punct :: Case1 Char
    , plain :: Case1 String
    , markup :: Case1 String
    , dateTime :: Case2 (Record JsonDateTimeRow) (Maybe (Record JsonDateTimeRow))
    , clock :: Case1 (Record ClockRow)
    , diary :: Case1 (Record DiaryRow)
    , break :: Case
    , marked :: Case2 (Array (Variant MarkupKeyRow)) String
    , fnref :: Case2 String (Maybe String) -- FIXME: since using Words here is causing recursion to fail
    , entity :: Case1 String
    , empty :: Case
    -- , join :: Words /\ Words
    )


readWords :: Foreign -> F Words
readWords =
    readMatchImpl
        (Proxy :: _ WordsRow)
        { marked : Variant.use2 $ Marked <<< rowArrayToMarkupKey
        , link : Variant.use2 Link
        , linkRaw : Variant.use1 RawLink
        , image : Variant.use1 Image
        , imageRaw : Variant.use1 RawImage
        , punct : Variant.use1 $ Punct <<< codePointFromChar
        , plain : Variant.use1 Plain
        , markup : Variant.use1 Markup
        , dateTime : Variant.use2 $ \start end -> DateTime { start : load start, end : load <$> end }
        , diary : Variant.use1 $ DiaryW <<< load
        , clock : Variant.use1 $ ClockW <<< wrap
        , break : Variant.use Break
        , entity : Variant.use1 Entity
        , fnref : Variant.use2 $ \label def -> FootnoteRef { label, def }
        , empty : Variant.use EmptyW
        -- , join : Variant.use2 JoinW
        }


wordsToVariant :: Words -> Variant WordsRow
wordsToVariant = case _ of
    Marked key s -> Variant.select2 (Proxy :: _ "marked") (markupKeyToRowArray key) s
    Link url mbStr -> Variant.select2 (Proxy :: _ "link") url mbStr
    RawLink url -> Variant.select1 (Proxy :: _ "linkRaw") url
    Image url -> Variant.select1 (Proxy :: _ "image") url
    RawImage url -> Variant.select1 (Proxy :: _ "imageRaw") url
    Punct _ -> Variant.select1 (Proxy :: _ "punct") $ ':' -- FIXME
    Plain p -> Variant.select1 (Proxy :: _ "plain") p
    Markup mup -> Variant.select1 (Proxy :: _ "markup") mup
    DateTime { start, end } -> Variant.select2 (Proxy :: _ "dateTime") (convert start) (convert <$> end)
    ClockW clock -> Variant.select1 (Proxy :: _ "clock") $ unwrap clock
    DiaryW diary -> Variant.select1 (Proxy :: _ "diary") $ convert diary
    Break -> Variant.select (Proxy :: _ "break")
    FootnoteRef { label, def } -> Variant.select2 (Proxy :: _ "fnref") label def
    Entity entity -> Variant.select1 (Proxy :: _ "entity") $ entity
    JoinW wA wB -> Variant.select1 (Proxy :: _ "plain") "JOIN" -- FIXME: (we're flattening words before exporting, aren't we?)
    EmptyW -> Variant.select (Proxy :: _ "empty")


wordsFromVariant :: Variant WordsRow -> Words
wordsFromVariant =
    Variant.match
        { marked : Variant.uncase2 >>> lmap rowArrayToMarkupKey >>> Tuple.uncurry Marked
        , link : Variant.uncase2 >>> Tuple.uncurry Link
        , linkRaw : Variant.uncase1 >>> RawLink
        , image : Variant.uncase1 >>> Image
        , imageRaw : Variant.uncase1 >>> RawImage
        , punct : Variant.uncase1 >>> codePointFromChar >>> Punct
        , plain : Variant.uncase1 >>> Plain
        , markup : Variant.uncase1 >>> Markup
        , entity : Variant.uncase1 >>> Entity
        , dateTime : Variant.uncase2 >>> bimap load (map load) >>> Tuple.uncurry (\start end -> { start, end }) >>> DateTime
        , clock : Variant.uncase1 >>> wrap >>> ClockW
        , diary : Variant.uncase1 >>> load >>> DiaryW
        , break : Variant.uncase Break
        , fnref : Variant.uncase2 >>> Tuple.uncurry (\label def -> { label, def }) >>> FootnoteRef
        -- , join : Variant.uncase2 JoinW  -- FIXME
        , empty : Variant.uncase EmptyW
        }


instance ReadForeign Words where readImpl = readImplVar
instance WriteForeign Words where writeImpl = writeImplVar
instance JsonOverVariant WordsRow Words where
    readForeign = readWords
    toVariant = wordsToVariant
    fromVariant = wordsFromVariant


type CookieRow =
    ( split :: Case
    , percent :: Case
    , pie :: Case
    )


readCookie :: Foreign -> F Cookie
readCookie =
    readMatchImpl
        (Proxy :: _ CookieRow)
        { split : Variant.use Split
        , percent : Variant.use Percent
        , pie : Variant.use Pie
        }


cookieToVariant :: Cookie -> Variant CookieRow
cookieToVariant = case _ of
    Split -> Variant.select (Proxy :: _ "split")
    Percent -> Variant.select (Proxy :: _ "percent")
    Pie -> Variant.select (Proxy :: _ "pie")


cookieFromVariant :: Variant CookieRow -> Cookie
cookieFromVariant =
    Variant.match
        { split : Variant.uncase Split
        , percent : Variant.uncase Percent
        , pie : Variant.uncase Pie
        }


instance ReadForeign Cookie where readImpl = readImplVar
instance WriteForeign Cookie where writeImpl = writeImplVar
instance JsonOverVariant CookieRow Cookie where
    readForeign = readCookie
    toVariant = cookieToVariant
    fromVariant = cookieFromVariant


type PriorityRow =
    ( alpha :: Case1 Char
    , num :: Case1 Int
    )


readPriority :: Foreign -> F Priority
readPriority =
    readMatchImpl
        (Proxy :: _ PriorityRow)
        { alpha : Variant.use1 Alpha
        , num : Variant.use1 Num
        }


priorityToVariant :: Priority -> Variant PriorityRow
priorityToVariant = case _ of
    Alpha a -> Variant.select1 (Proxy :: _ "alpha") a
    Num n -> Variant.select1 (Proxy :: _ "num") n


priorityFromVariant :: Variant PriorityRow -> Priority
priorityFromVariant =
    Variant.match
        { alpha : Variant.uncase1 >>> Alpha
        , num : Variant.uncase1 >>> Num
        }


instance ReadForeign Priority where readImpl = readImplVar
instance WriteForeign Priority where writeImpl = writeImplVar
instance JsonOverVariant PriorityRow Priority where
    readForeign = readPriority
    toVariant = priorityToVariant
    fromVariant = priorityFromVariant


type TodoRow =
    ( todo :: Case
    , doing :: Case
    , done :: Case
    , now :: Case
    , next :: Case
    , custom :: Case1 String
    )


readTodo :: Foreign -> F Todo
readTodo =
    readMatchImpl
        (Proxy :: _ TodoRow)
        { todo   : Variant.use Todo
        , doing  : Variant.use Doing
        , done   : Variant.use Done
        , now    : Variant.use Now
        , next   : Variant.use Next
        , custom : Variant.use1 CustomKW
        }


todoToVariant :: Todo -> Variant TodoRow
todoToVariant = case _ of
    Todo  -> Variant.select (Proxy :: _ "todo")
    Doing -> Variant.select (Proxy :: _ "doing")
    Done  -> Variant.select (Proxy :: _ "done")
    Now   -> Variant.select (Proxy :: _ "now")
    Next  -> Variant.select (Proxy :: _ "next")
    CustomKW s -> Variant.select1 (Proxy :: _ "custom") s


todoFromVariant :: Variant TodoRow -> Todo
todoFromVariant =
    Variant.match
        { todo : Variant.uncase Todo
        , doing : Variant.uncase Doing
        , done : Variant.uncase Done
        , now : Variant.uncase Now
        , next : Variant.uncase Next
        , custom : Variant.uncase1 >>> CustomKW
        }


instance ReadForeign Todo where readImpl = readImplVar
instance WriteForeign Todo where writeImpl = writeImplVar
instance JsonOverVariant TodoRow Todo where
    readForeign = readTodo
    toVariant = todoToVariant
    fromVariant = todoFromVariant


type ListTypeRow =
    ( bulleted :: Case
    , plussed :: Case
    , numbered :: Case
    , numberedFrom :: Case1 Int
    , hyphened :: Case
    , alphed :: Case
    , prefixed :: Case1 String
    )


readListType :: Foreign -> F ListType
readListType =
    readMatchImpl
        (Proxy :: _ ListTypeRow)
        { bulleted : Variant.use Bulleted
        , plussed : Variant.use Plussed
        , numbered : Variant.use Numbered
        , numberedFrom : Variant.use1 NumberedFrom
        , hyphened : Variant.use Hyphened
        , alphed : Variant.use Alphed
        , prefixed : Variant.use1 Prefixed
        }


listTypeToVariant :: ListType -> Variant ListTypeRow
listTypeToVariant = case _ of
    Bulleted -> Variant.select (Proxy :: _ "bulleted")
    Plussed -> Variant.select (Proxy :: _ "plussed")
    Numbered -> Variant.select (Proxy :: _ "numbered")
    NumberedFrom n -> Variant.select1 (Proxy :: _ "numberedFrom") n
    Hyphened -> Variant.select (Proxy :: _ "hyphened")
    Alphed -> Variant.select (Proxy :: _ "alphed")
    Prefixed s -> Variant.select1 (Proxy :: _ "prefixed") s


listTypeFromVariant :: Variant ListTypeRow -> ListType
listTypeFromVariant =
    Variant.match
        { bulleted : Variant.uncase Bulleted
        , plussed : Variant.uncase Plussed
        , numbered : Variant.uncase Numbered
        , numberedFrom : Variant.uncase1 >>> NumberedFrom
        , hyphened : Variant.uncase Hyphened
        , alphed : Variant.uncase Alphed
        , prefixed : Variant.uncase1 >>> Prefixed
        }


instance ReadForeign ListType where readImpl = readImplVar
instance WriteForeign ListType where writeImpl = writeImplVar
instance JsonOverVariant ListTypeRow ListType where
    readForeign = readListType
    toVariant = listTypeToVariant
    fromVariant = listTypeFromVariant


type IntervalRow =
    ( hour :: Case
    , day :: Case
    , week :: Case
    , month :: Case
    , year :: Case
    )


readInterval :: Foreign -> F Interval
readInterval =
    readMatchImpl
        (Proxy :: _ IntervalRow)
        { hour : Variant.use Hour
        , day : Variant.use Day
        , week : Variant.use Week
        , month : Variant.use Month
        , year : Variant.use Year
        }


intervalToVariant :: Interval -> Variant IntervalRow
intervalToVariant = case _ of
    Hour  -> Variant.select (Proxy :: _ "hour")
    Day   -> Variant.select (Proxy :: _ "day")
    Week  -> Variant.select (Proxy :: _ "week")
    Month -> Variant.select (Proxy :: _ "month")
    Year  -> Variant.select (Proxy :: _ "year")


intervalFromVariant :: Variant IntervalRow -> Interval
intervalFromVariant =
    Variant.match
        { hour : Variant.uncase Hour
        , day : Variant.uncase Day
        , week : Variant.uncase Week
        , month : Variant.uncase Month
        , year : Variant.uncase Year
        }


instance ReadForeign Interval where readImpl = readImplVar
instance WriteForeign Interval where writeImpl = writeImplVar
instance JsonOverVariant IntervalRow Interval where
    readForeign = readInterval
    toVariant = intervalToVariant
    fromVariant = intervalFromVariant


type RepeaterModeRow =
    ( single :: Case
    , jump :: Case
    , fromToday :: Case
    )


readRepeaterMode :: Foreign -> F RepeaterMode
readRepeaterMode =
    readMatchImpl
        (Proxy :: _ RepeaterModeRow)
        { single : Variant.use Single
        , jump : Variant.use Jump
        , fromToday : Variant.use FromToday
        }


repeaterModeToVariant :: RepeaterMode -> Variant RepeaterModeRow
repeaterModeToVariant = case _ of
    Single    -> Variant.select (Proxy :: _ "single")
    Jump      -> Variant.select (Proxy :: _ "jump")
    FromToday -> Variant.select (Proxy :: _ "fromToday")


repeaterModeFromVariant :: Variant RepeaterModeRow -> RepeaterMode
repeaterModeFromVariant =
    Variant.match
        { single : Variant.uncase Single
        , jump : Variant.uncase Jump
        , fromToday : Variant.uncase FromToday
        }


instance ReadForeign RepeaterMode where readImpl = readImplVar
instance WriteForeign RepeaterMode where writeImpl = writeImplVar
instance JsonOverVariant RepeaterModeRow RepeaterMode where
    readForeign = readRepeaterMode
    toVariant = repeaterModeToVariant
    fromVariant = repeaterModeFromVariant


type DelayModeRow =
    ( one :: Case
    , all :: Case
    )


readDelayMode :: Foreign -> F DelayMode
readDelayMode =
    readMatchImpl
        (Proxy :: _ DelayModeRow)
        { one : Variant.use One
        , all : Variant.use All
        }


delayModeToVariant :: DelayMode -> Variant DelayModeRow
delayModeToVariant = case _ of
    One -> Variant.select (Proxy :: _ "one")
    All -> Variant.select (Proxy :: _ "all")


delayModeFromVariant :: Variant DelayModeRow -> DelayMode
delayModeFromVariant mode =
    flip Variant.match mode $
        { one : const One
        , all : const All
        }


instance ReadForeign DelayMode where readImpl = readImplVar
instance WriteForeign DelayMode where writeImpl = writeImplVar
instance JsonOverVariant DelayModeRow DelayMode where
    readForeign = readDelayMode
    toVariant = delayModeToVariant
    fromVariant = delayModeFromVariant


instance ReadForeign Drawer where readImpl = readImplNT
instance WriteForeign Drawer where writeImpl = writeImplNT


-- instance ReadForeign OrgDateTime where readImpl f = readImpl f <#> wrap
-- instance WriteForeign OrgDateTime where writeImpl = unwrap >>> writeImpl


-- instance ReadForeign OrgTime where readImpl f = readImpl f <#> wrap
-- instance WriteForeign OrgTime where writeImpl = unwrap >>> writeImpl


instance ReadForeign Repeater where readImpl = readImplNT
instance WriteForeign Repeater where writeImpl = writeImplNT


-- instance ReadForeign OrgDoc where readImpl f = readImpl f <#> wrap
-- instance WriteForeign OrgDoc where writeImpl = unwrap >>> writeImpl


-- instance ReadForeign Section where readImpl f = readImpl f <#> wrap
-- instance WriteForeign Section where writeImpl = unwrap >>> writeImpl


type DelayRow =
    ( mode :: Variant DelayModeRow
    , value :: Int
    , interval :: Interval
    )


convertDelay :: Delay -> Record DelayRow
convertDelay = unwrap >>>
    case _ of
        { mode, value, interval } ->
            { mode : toVariant mode
            , value
            , interval
            }


loadDelay :: Record DelayRow -> Delay
loadDelay =
    case _ of
        { mode, value, interval } ->
            wrap
                { mode : fromVariant mode
                , value
                , interval
                }


instance ReadForeign Delay where readImpl = readImplNT
instance WriteForeign Delay where writeImpl = writeImplNT
instance JsonOverRow DelayRow Delay where
    convert = convertDelay
    load = loadDelay


type JsonTimeRow =
    ( hour :: Int
    , minute :: Int
    , second :: Int
    , millisecond :: Int
    -- TODO: zone :: String
    )


convertTime :: Time -> Record JsonTimeRow
convertTime t =
    { hour : Time.hour t # fromEnum
    , minute : Time.minute t # fromEnum
    , second : Time.second t # fromEnum
    , millisecond : Time.millisecond t # fromEnum
    }


loadTime :: Record JsonTimeRow -> Time
loadTime rec =
    Time
        (toEnum rec.hour # fromMaybe bottom)
        (toEnum rec.minute # fromMaybe bottom)
        (toEnum rec.second # fromMaybe bottom)
        (toEnum rec.millisecond # fromMaybe bottom)


-- instance ReadForeign Time where readImpl = readImplRow
-- instance WriteForeign Time where writeImpl = writeImplRow
instance JsonOverRow JsonTimeRow Time where
    convert = convertTime
    load = loadTime


type JsonTimeRangeRow =
    ( start :: Record JsonTimeRow
    , end :: Maybe (Record JsonTimeRow)
    )


convertTimeRange :: OrgTimeRange -> Record JsonTimeRangeRow
convertTimeRange t =
    { start : convert  $ _.start $ unwrap t
    , end :   convert <$> (_.end $ unwrap t)
    }


loadTimeRange :: Record JsonTimeRangeRow -> OrgTimeRange
loadTimeRange rec =
    OrgTimeRange
        { start : load rec.start
        , end : load <$> rec.end
        }


instance JsonOverRow JsonTimeRangeRow OrgTimeRange where
    convert = convertTimeRange
    load = loadTimeRange


type JsonDateTimeRow =
    ( day :: Int
    , month :: Int
    , year :: Int
    , time :: Maybe (Record JsonTimeRangeRow)
    , repeat :: Maybe Repeater
    , delay :: Maybe Delay
    , active :: Boolean
    )


convertToDateTime :: OrgDateTime -> Record JsonDateTimeRow
convertToDateTime = unwrap >>> case _ of
    { date, time, repeat, delay, active } ->
        { day : fromEnum $ D.day date
        , month : fromEnum $ D.month date
        , year : fromEnum $ D.year date
        , time : convert <$> time
        , delay
        , repeat
        , active
        }


loadDateTime :: Record JsonDateTimeRow -> OrgDateTime
loadDateTime =
    case _ of
        { day, month, year, time, repeat, delay, active } ->
            wrap
                { date :
                    canonicalDate
                        (toEnum year # fromMaybe bottom)
                        (toEnum month # fromMaybe bottom)
                        (toEnum day # fromMaybe bottom)
                , time : load <$> time
                , delay
                , repeat
                , active
                }


instance JsonOverRow JsonDateTimeRow OrgDateTime where
    convert = convertToDateTime
    load = loadDateTime


convertDateTimeNT :: OrgDateTime -> JsonDateTime
convertDateTimeNT = convert >>> wrap


loadDateTimeNT :: JsonDateTime -> OrgDateTime
loadDateTimeNT = unwrap >>> load


newtype JsonDateTime = JsonDateTime (Record JsonDateTimeRow)


derive instance Newtype JsonDateTime _


instance ReadForeign JsonDateTime where readImpl = readImplNT
instance WriteForeign JsonDateTime where writeImpl = writeImplNT


newtype JsonSectionId = SectionId (Array Int)


derive instance Newtype JsonSectionId _


derive newtype instance Eq JsonSectionId
derive newtype instance Ord JsonSectionId


instance ReadForeign JsonSectionId where readImpl = readImplNT
instance WriteForeign JsonSectionId where writeImpl = writeImplNT


type PlanningRow =
    ( closed :: Maybe JsonDateTime
    , deadline :: Maybe JsonDateTime
    , scheduled :: Maybe JsonDateTime
    , timestamp :: Maybe JsonDateTime
    )


convertPlanning :: Planning -> Record PlanningRow
convertPlanning = unwrap >>> case _ of
    pl ->
        { closed    : convertDateTimeNT <$> pl.closed
        , deadline  : convertDateTimeNT <$> pl.deadline
        , scheduled : convertDateTimeNT <$> pl.scheduled
        , timestamp : convertDateTimeNT <$> pl.timestamp
        }


loadPlanning :: Record PlanningRow -> Planning
loadPlanning pl =
    wrap
        { closed : loadDateTimeNT <$> pl.closed
        , deadline : loadDateTimeNT <$> pl.deadline
        , scheduled : loadDateTimeNT <$> pl.scheduled
        , timestamp : loadDateTimeNT <$> pl.timestamp
        }


instance JsonOverRow PlanningRow Planning where
    convert = convertPlanning
    load = loadPlanning


-- convertDoc :: OrgDoc -> Record DocRow
-- convertOrgFile :: OrgFile -> Record FileRow


type LogBookSubjectRow =
    ( state :: Case3 (Variant TodoRow) (Variant TodoRow) JsonDateTime
    , reschedule :: Case2 JsonDateTime JsonDateTime
    , note :: Case1 JsonDateTime
    , other :: Case2 (Array Words) (Array JsonDateTime)
    )


readEntrySubject :: Foreign -> F LogBookEntrySubject
readEntrySubject =
    readMatchImpl
        (Proxy :: _ LogBookSubjectRow)
        { state : Variant.use3 \fromVar toVar jsonTimestamp ->
                        StateChange (fromVariant fromVar) (fromVariant toVar) (loadDateTimeNT jsonTimestamp)
        , reschedule : Variant.use2 \from to -> Reschedule (loadDateTimeNT from) (loadDateTimeNT to)
        , note : Variant.use1 $ NoteTaken <<< loadDateTimeNT
        , other : Variant.use2 \words stamps -> Other words $ loadDateTimeNT <$> stamps
        }


entrySubjectToVariant :: LogBookEntrySubject -> Variant LogBookSubjectRow
entrySubjectToVariant = case _ of
    StateChange from to timestamp -> Variant.select3 (Proxy :: _ "state") (toVariant from) (toVariant to) (convertDateTimeNT timestamp)
    Reschedule from to -> Variant.select2 (Proxy :: _ "reschedule") (convertDateTimeNT from) (convertDateTimeNT to)
    NoteTaken ts -> Variant.select1 (Proxy :: _ "note") $ convertDateTimeNT ts
    Other words stamps -> Variant.select2 (Proxy :: _ "other") words $ convertDateTimeNT <$> stamps


entrySubjectFromVariant :: Variant LogBookSubjectRow -> LogBookEntrySubject
entrySubjectFromVariant =
    Variant.match
        { state : Variant.uncase3 >>> \(fromVar /\ toVar /\ jsonTimestamp) ->
                        StateChange (fromVariant fromVar) (fromVariant toVar) (loadDateTimeNT jsonTimestamp)
        , reschedule : Variant.uncase2 >>> bimap loadDateTimeNT loadDateTimeNT >>> Tuple.uncurry Reschedule
        , note : Variant.uncase1 >>> loadDateTimeNT >>> NoteTaken
        , other : Variant.uncase2 >>> map (map loadDateTimeNT) >>> Tuple.uncurry Other
        }


instance ReadForeign LogBookEntrySubject where readImpl = readImplVar
instance WriteForeign LogBookEntrySubject where writeImpl = writeImplVar
instance JsonOverVariant LogBookSubjectRow LogBookEntrySubject where
    readForeign = readEntrySubject
    toVariant = entrySubjectToVariant
    fromVariant = entrySubjectFromVariant


type LogBookEntryRow =
    ( subject :: Variant LogBookSubjectRow
    , continuation :: Array (Array Words)
    )


instance ReadForeign LogBookEntry where readImpl = readImplRow
instance WriteForeign LogBookEntry where writeImpl = writeImplRow
instance JsonOverRow LogBookEntryRow LogBookEntry where
    convert = unwrap >>> \{ subject, continuation } -> { subject : toVariant subject, continuation }
    load { subject, continuation } = wrap { subject : fromVariant subject, continuation }


type DocRow =
    ( blocks ::
        Array
            { keywords :: JsonKeywords String
            , block :: Variant BlockRow
            }
    , sections :: Array JsonSectionId
    )


type SectionRow =
    ( id :: JsonSectionId
     -- FIXME: We may use original types instead of `Variant` here and below since `readForeign`/`writeForeign` are implemented for them
    , todo :: Maybe (Variant TodoRow)
    , priority :: Maybe (Variant PriorityRow)
    , cookie :: Maybe (Variant CookieRow)
    , check :: Maybe (Variant CheckRow)
    , heading :: Array Words
    , level :: Int
    , planning :: Record PlanningRow
    , props :: JsonProperties String
    , logbook :: Array (Record LogBookEntryRow)
    , comment :: Boolean
    , drawers :: Array Drawer
    , doc :: Record DocRow
    , tags :: Array String
    )


type FileRow =
    ( meta  :: JsonKeywords String
    , props :: JsonProperties String
    , doc :: Record DocRow
    , sections ::
        Array
            { id :: JsonSectionId
            , section :: Record SectionRow
            }
    )


type SectionsMap = Map JsonSectionId (Record SectionRow)


sectionsToArray :: SectionsMap -> Array { id :: JsonSectionId, section :: Record SectionRow }
sectionsToArray = Map.toUnfoldable >>> map \(id /\ section) -> { id, section }


sectionsFromArray :: Array { id :: JsonSectionId, section :: Record SectionRow } -> SectionsMap
sectionsFromArray = map (\{ id, section } -> id /\ section) >>> Map.fromFoldable


emptyPlanning :: Planning
emptyPlanning =
    Planning
        { closed : Nothing
        , deadline : Nothing
        , scheduled : Nothing
        , timestamp : Nothing
        }


emptyDoc :: OrgDoc
emptyDoc =
    OrgDoc
        { zeroth : []
        , sections : []
        }


emptySection :: Section
emptySection =
    Section
        { todo: Nothing
        , priority : Nothing
        , cookie : Nothing
        , check : Nothing
        , heading : NEA.singleton $ EmptyW
        , level : -1
        , tags : []
        , planning : emptyPlanning
        , props : Prop.empty
        , logbook : Nothing
        , drawers : []
        , comment : false
        , doc : emptyDoc
        }


convertSection :: JsonSectionId -> Section -> Record SectionRow /\ SectionsMap
convertSection sectionId (Section section) =
    let convertedDoc /\ sectionsMap = convertDoc sectionId section.doc
    in
        { id : sectionId
        , todo : toVariant <$> section.todo
        , priority : toVariant <$> section.priority
        , cookie : toVariant <$> section.cookie
        , check : toVariant <$> section.check
        , heading : exportWords section.heading
        , level : section.level
        , planning : convert section.planning
        , logbook : fromMaybe [] $ map convert <$> unwrap <$> section.logbook
        , props : Prop.toJson section.props
        , drawers : section.drawers
        , tags : section.tags
        , comment : section.comment
        , doc : convertedDoc
        }
    /\ sectionsMap


loadSection :: SectionsMap -> Record SectionRow -> Section
loadSection allSections section =
    Section
        { todo : fromVariant <$> section.todo
        , priority : fromVariant <$> section.priority
        , cookie : fromVariant <$> section.cookie
        , check : fromVariant <$> section.check
        , heading : importWords section.heading
        , level : section.level
        , tags : section.tags
        , planning : load section.planning
        , logbook : if Array.length section.logbook > 0
                        then Just $ LogBook $ load <$> section.logbook
                        else Nothing
        , drawers : section.drawers
        , props : Prop.fromJson section.props
        , comment : section.comment
        , doc : loadDoc allSections section.doc
        }


-- instance ReadForeign Section where
--     readImpl f = (readImpl f :: F (Record SectionRow)) <#> loadSection (SectionsMap Map.empty)


-- instance JsonOverRow DocRow OrgDoc where
--     convert = convertSection
--     load = loadSection


collectSections :: JsonSectionId -> Array Section -> Array JsonSectionId /\ SectionsMap
collectSections (SectionId parentId) sections =
    let
        sectionsIdsAndInnerMaps =
            sections
                # Array.mapWithIndex
                    (\idx section ->
                        let
                            sectionId = SectionId $ parentId <> [ idx ]
                            convertedSection /\ innerSections = convertSection sectionId section
                        in
                            sectionId /\ (innerSections # Map.insert sectionId convertedSection)
                    )
        sectionsIds = Tuple.fst <$> sectionsIdsAndInnerMaps
        sectionsMap = Array.foldl Map.union Map.empty $ Tuple.snd <$> sectionsIdsAndInnerMaps
    in sectionsIds /\ sectionsMap


convertDoc :: JsonSectionId -> OrgDoc -> Record DocRow /\ SectionsMap
convertDoc parentId (OrgDoc doc) =
    let
        (sectionsIds /\ sectionsMap) = collectSections parentId doc.sections
        collectKeywords = collectKeywords' []
        collectKeywords'
            :: Array (JsonKeywordOrPropRec String)
            -> Block
            -> { keywords :: JsonKeywords String, block :: Variant BlockRow }
        collectKeywords' prev =
            case _ of
                WithKeyword keyword block ->
                    collectKeywords' (Array.snoc prev $ KW.toRec keyword) block
                block ->
                    { keywords : JsonKeywords prev, block : toVariant block }
    in
    (
        { blocks : collectKeywords <$> flattenBlocks doc.zeroth
        , sections : sectionsIds
        }
    /\
        sectionsMap
    )


-- instance ReadForeign OrgDoc where
--     readImpl f = (readImpl f :: F (Record DocRow)) <#> loadDoc Map.empty


loadDoc :: SectionsMap -> Record DocRow -> OrgDoc
loadDoc allSections doc =
    OrgDoc
        { zeroth : blockWithKeywords <$> doc.blocks
        , sections : loadOrEmpty <$> doc.sections
        }
    where
        blockWithKeywords
            :: { keywords :: JsonKeywords String, block :: Variant BlockRow }
            -> Block
        blockWithKeywords { keywords, block } =
            case Array.uncons $ unwrap keywords of
                Just { head, tail } ->
                    WithKeyword (KW.fromRec head) $ blockWithKeywords { keywords : wrap tail, block }
                Nothing ->
                    fromVariant block
        loadOrEmpty sectionId =
            Map.lookup sectionId allSections
                <#> loadSection allSections
                 #  fromMaybe emptySection


-- instance JsonOverRow DocRow OrgDoc where
--     convert = convertDoc
--     load = loadDoc


convertFile :: OrgFile -> Record FileRow
convertFile (OrgFile { meta, props, doc }) =
    let convertedDoc /\ sectionsMap = convertDoc (SectionId [ 0 ]) doc
    in
    { meta  : KW.toJson meta
    , props : Prop.toJson props
    , doc : convertedDoc
    , sections : sectionsToArray sectionsMap
    }


loadFile :: Record FileRow -> OrgFile
loadFile file =
    OrgFile
        { meta  : KW.fromJson file.meta
        , props : Prop.fromJson file.props
        , doc : loadDoc (sectionsFromArray file.sections) file.doc
        }


-- convertFileNT :: OrgFile -
-- convertFileNT = convert >>> wrap


-- loadFileNT :: Record FileRow -> OrgFile
-- loadFileNT = unwrap >>> load


instance JsonOverRow FileRow OrgFile where
    convert = convertFile
    load = loadFile


instance JsonOverRow (JsonPropertyRow String) (OrgProperty String) where
    convert = Prop.toRec
    load = Prop.fromRec


-- instance Newtype (Array Int) JsonSectionId


instance ReadForeign OrgFile where readImpl = readImplRow
instance WriteForeign OrgFile where writeImpl = writeImplRow


flattenWords :: Array Words -> Array Words
flattenWords =
    flattenJoins $ case _ of
        JoinW wa wb -> Just $ wa /\ wb
        _ -> Nothing


flattenBlocks :: Array Block -> Array Block
flattenBlocks =
    flattenJoins $ case _ of
        JoinB ba bb -> Just $ ba /\ bb
        _ -> Nothing


flattenJoins :: forall a. (a -> Maybe (a /\ a)) -> Array a -> Array a
flattenJoins isJoin =
    Array.concatMap flattenJoin
    where
        flattenJoin item =
            case isJoin item of
                Just (joinA /\ joinB) -> [ joinA, joinB ]
                Nothing -> [ item ]