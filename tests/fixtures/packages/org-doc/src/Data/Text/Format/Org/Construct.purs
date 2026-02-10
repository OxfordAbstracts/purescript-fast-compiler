module Data.Text.Format.Org.Construct where

import Prelude

import Data.Maybe (Maybe(..), fromMaybe)
import Data.Map (empty, insert, size, fromFoldable) as Map
import Data.Enum (class BoundedEnum)
import Data.Tuple (curry, uncurry)
import Data.Foldable (class Foldable)
import Data.Unfoldable (class Unfoldable)
import Data.Tuple.Nested ((/\), type (/\))
import Data.Array ((:))
import Data.Array (toUnfoldable, length, mapWithIndex, singleton, delete, foldl, foldr, snoc, intersperse, last, modifyAt) as Array
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NEA
import Data.String (Pattern(..))
import Data.String (joinWith, toUpper, split) as String
import Data.Newtype (unwrap, wrap)
import Data.Time (Time(..), hour, minute, second) as T
import Data.Date (Date, canonicalDate) as T
import Data.Enum (toEnum, fromEnum)
import Data.Int (fromString) as Int
import Data.FunctorWithIndex (mapWithIndex)


import Data.Text.Format.Org.Types
import Data.Text.Format.Org.Path (Path)
import Data.Text.Format.Org.Path as P
import Data.Text.Format.Org.Property (OrgProperty)
import Data.Text.Format.Org.Property as Prop
import Data.Text.Format.Org.Keyword (OrgKeyword)
import Data.Text.Format.Org.Keyword as KW --as Keywords



-- | Create empty `OrgFile`
empty :: OrgFile
empty = f emptyDoc


emptyDoc :: OrgDoc
emptyDoc =
    OrgDoc { zeroth : [], sections : [] }


-- | Create `OrgFile` with empty `meta` and given `OrgDoc` as its root
f :: OrgDoc -> OrgFile
f = f_ [] []


-- | Create `OrgFile` with given `meta` keywords and properties and given `OrgDoc` as its root
f_ :: Array (OrgKeyword String) -> Array (OrgProperty String) -> OrgDoc -> OrgFile
f_ keywords props doc =
    OrgFile { meta : KW.make keywords, props : Prop.make props, doc }


-- | create `OrgDoc` from given `Section`s without any preceding blocks
ds :: Array Section -> OrgDoc
ds sections = OrgDoc { zeroth : [], sections }


-- | create `OrgDoc` from one given `Section` without any preceding blocks
ds1 :: Section -> OrgDoc
ds1 = ds <<< Array.singleton


-- | create `OrgDoc` from given `Block`s without any following sections
db :: Array Block -> OrgDoc
db blocks = OrgDoc { zeroth : blocks, sections : [] }


-- | create `OrgDoc` from one given `Block` without any following sections
db1 :: Block -> OrgDoc
db1 = db <<< Array.singleton


-- | create `OrgDoc` from given `Block`s and `Section`s
dbs :: Array Block -> Array Section -> OrgDoc
dbs blocks sections = OrgDoc { zeroth : blocks, sections }



-- | Root document of the file
docf :: OrgFile -> OrgDoc
docf (OrgFile { doc }) = doc


-- | Root document of the section
docs :: Section -> OrgDoc
docs (Section { doc }) = doc


-- | Get all the zeroth blocks of given document
blocks :: OrgDoc -> Array Block
blocks (OrgDoc { zeroth }) = zeroth


-- | Get all the sections of given document
sections :: OrgDoc -> Array Section
sections (OrgDoc { sections }) = sections


-- | How many sections does this `OrgDoc` have
sectionsn :: OrgDoc -> Int
sectionsn = sections >>> Array.length


-- | How many blocks does this `OrgDoc` have
blocksn :: OrgDoc -> Int
blocksn = blocks >>> Array.length


-- | Add meta keyword to the `OrgFile` as the last one
meta_kw :: OrgKeyword String -> OrgFile -> OrgFile
meta_kw kw (OrgFile { meta, props, doc }) =
    OrgFile
        { meta : KW.snoc meta kw
        , props, doc
        }


-- | Add meta keyword to the `OrgFile` as the first one
meta_kw_ :: OrgKeyword String -> OrgFile -> OrgFile
meta_kw_ kw (OrgFile { meta, props, doc }) =
    OrgFile
        { meta : KW.cons kw meta
        , props, doc
        }


-- | Add property to the `OrgFile` properties drawer as the last one
meta_prop :: OrgProperty String -> OrgFile -> OrgFile
meta_prop prop (OrgFile { meta, props, doc }) =
    OrgFile
        { props : Prop.snoc props prop
        , meta, doc
        }


-- | Add property to the `OrgFile` properties drawer as the first one
meta_prop_ :: OrgProperty String -> OrgFile -> OrgFile
meta_prop_ prop (OrgFile { meta, props, doc }) =
    OrgFile
        { props : props # Prop.cons prop
        , meta, doc
        }


data ProgressStep = Progress String
data FinishStep = Finish String


todoSequence :: Array ProgressStep -> Array FinishStep -> OrgFile -> OrgFile
todoSequence pss fss =
    meta_kw_ $ KW.kw "SEQ_TODO" $ String.joinWith " " (pssToString <$> pss) <> " | " <> String.joinWith " " (fssToString <$> fss)
    where
     pssToString (Progress str) = String.toUpper str
     fssToString (Finish str) = String.toUpper str


quote :: Array Words -> Block
quote = Of Quote <<< __neafws


example :: Array Words -> Block
example = Of Example <<< __neafws


code :: String -> Block
code str = code' [ Plain str ]


code' :: Array Words -> Block
code' = Of (Code Nothing) <<< __neafws


codeIn :: String -> String -> Block
codeIn lang str = codeIn' lang [ Plain str ]


codeIn' :: String -> Array Words -> Block
codeIn' lang = Of (Code $ Just $ Language lang) <<< __neafws


bcomment :: Array String -> Block
bcomment ws = Of Comment $ __neafws $ Array.intersperse Break $ Plain <$> ws


verse :: Array Words -> Block
verse = Of Verse <<< __neafws


bcenter :: Array Words -> Block
bcenter = Of Center <<< __neafws


bexport :: Array Words -> Block
bexport = Of Export <<< __neafws


list :: ListType -> Array Item -> Block
list lt = List <<< __items lt


det_item :: DetachedListItem -> Block
det_item = DetachedItem


item :: Array Words -> Item
item ws =
    Item
        { check : Nothing, counter : Nothing, tag : Nothing, drawers : [] }
        (__neafws ws)
        Nothing


item1 :: Words -> Item
item1 = item <<< Array.singleton


table :: Array TableRow -> Block
table = Table Nothing <<< __neaf tbreak


tablef :: TableFormat -> Array TableRow -> Block
tablef format = Table (Just format) <<< __neaf tbreak


tbreak :: TableRow
tbreak = BreakT Nothing


tbreak_c :: TableCustomBreak -> TableRow
tbreak_c = BreakT <<< Just


tcol :: Array Words -> TableColumn
tcol = Column <<< __neafws


tcol1 :: Words -> TableColumn
tcol1 = tcol <<< Array.singleton


tskip :: TableColumn
tskip = Empty


trow :: Array TableColumn -> TableRow
trow = Row <<< __neaf Empty
-- trow = Row <<< __neaf Empty <<< map toColumn
--     where
--         toColumn [] = Empty
--         toColumn arr = Column $ __neafws arr


qrow :: Array Words -> TableRow
qrow items = trow $ tcol1 <$> items


qrow' :: Array String -> TableRow
qrow' items = qrow $ text <$> items


check :: Check -> Item  -> Item
check ch (Item opts ws is) =
    Item
        (opts { check = Just ch })
        ws
        is


count :: Int -> Item  -> Item
count cnt (Item opts ws is) =
    Item
        (opts { counter = Just $ Counter cnt })
        ws
        is


sub :: ListType -> Array Item -> Item -> Item
sub lt is (Item opts ws _) =
    Item
        opts
        ws
        $ Just
        $ __items lt is


tagi :: String -> Item -> Item
tagi tag (Item opts ws is) =
    Item
        (opts { tag = Just tag })
        ws
        is


idrawer :: String -> Array Words -> Item -> Item
idrawer name content (Item rec iws inner) =
    Item
        (rec
            { drawers =
                Array.snoc rec.drawers $ Drawer { name, content : __neafws content }
            }
        )
        iws
        inner


idrawer1 :: String -> Words -> Item -> Item
idrawer1 name = idrawer name <<< Array.singleton


bdrawer :: String -> Array Words -> Block
bdrawer name = bdrawer' <<< mk_drawer name


bdrawer1 :: String -> Words -> Block
bdrawer1 name = bdrawer name <<< Array.singleton


bdrawer' :: Drawer -> Block
bdrawer' = IsDrawer


-- | join two blocks in one
joinB :: Block -> Block -> Block
joinB = JoinB


-- | Block of a paragraph with given `Words`
para :: Array Words -> Block
para = Paragraph <<< __neafws


-- | Block of a paragraph with a single instance of `Words`
para1 :: Words -> Block
para1 = Paragraph <<< NEA.singleton


-- | Block with no text inside
blank :: Block
blank = para1 $ text ""


-- | Block only with a line break
br_blank :: Block
br_blank = para1 br


bold :: MarkupKey
bold = Bold


italic :: MarkupKey
italic = Italic


hilite :: MarkupKey
hilite = Highlight


under :: MarkupKey
under = Underline


verbatim :: MarkupKey
verbatim = Verbatim


icode :: MarkupKey
icode = InlineCode


strike :: MarkupKey
strike = Strike


both :: MarkupKey -> MarkupKey -> MarkupKey
both = And


b :: String -> Words
b = marked bold


i :: String -> Words
i = marked Italic


hl :: String -> Words
hl = marked Highlight


u :: String -> Words
u = marked Underline


v :: String -> Words
v = marked Verbatim


ic :: String -> Words
ic = marked InlineCode


s :: String -> Words
s = marked Strike


subs :: String -> Words
subs = marked Subscript


sups :: String -> Words
sups = marked Superscript


a :: String -> String -> Words
a = to <<< Remote


a' :: String -> Words
a' = ref <<< Remote


to :: LinkTarget -> String -> Words
to lt = Link lt <<< Just


ref :: LinkTarget -> Words
ref lt = Link lt Nothing


raw :: LinkTarget -> Words
raw = RawLink


rem :: String -> LinkTarget
rem = Remote


loc :: String -> LinkTarget
loc = Local


head :: String -> LinkTarget
head = Heading


irem :: String -> ImageSource
irem = RemoteSrc


iloc :: String -> ImageSource
iloc = LocalSrc


img :: String -> Words
img = Image <<< RemoteSrc


img_ :: ImageSource -> Words
img_ = Image


imgRaw_ :: ImageSource -> Words
imgRaw_ = RawImage


text :: String -> Words
text = Plain


br :: Words
br = Break


marked :: MarkupKey -> String -> Words
marked = Marked


icomment :: String -> Words
icomment = marked $ Inline IComment


entity :: String -> Words
entity = Entity


{-
atime :: T.Time -> OrgDateTime
atime = ?wh


itime :: T.Time -> OrgDateTime
itime = ?wh
-}


logbook_cont :: Array Words -> LogBook -> LogBook
logbook_cont contWords (LogBook items) =
    LogBook $ fromMaybe items $ Array.modifyAt (Array.length items - 1) (logbook_item_cont contWords) items


logbook_item_cont :: Array Words -> LogBookEntry -> LogBookEntry
logbook_item_cont contWords (LogBookEntry { subject, continuation }) =
    LogBookEntry { subject, continuation : Array.snoc continuation contWords }


-- | Create time from hours and minutes (exactly in this order) numbers with fallback to `bottom` of `Enum` for every invalid integer not in range
t :: Int -> Int -> T.Time
t h m = T.Time
            (toEnum h # fromMaybe bottom)
            (toEnum m # fromMaybe bottom)
            bottom
            bottom


-- | Create time from hours and minutes and seconds (exactly in this order) numbers with fallback to `bottom` of `Enum` for every invalid integer not in range
t' :: Int -> Int -> Int -> T.Time
t' h m s = T.Time
            (toEnum h # fromMaybe bottom)
            (toEnum m # fromMaybe bottom)
            (toEnum s # fromMaybe bottom)
            bottom


-- | Create a canonical date from year, month and day (exactly in this order) numbers with fallback to `bottom` of `Enum` for every invalid integer not in range
d :: Int -> Int -> Int -> T.Date
d year month day =
    T.canonicalDate
        (toEnum year # fromMaybe bottom)
        (toEnum month # fromMaybe bottom)
        (toEnum day # fromMaybe bottom)


clock :: T.Time -> Words
clock t = ClockW $ Clock
            { hour : fromEnum $ T.hour t
            , minute : fromEnum $ T.minute t
            , second : Just $ fromEnum $ T.second t
            }



clockB :: OrgDateTime -> OrgDateTime -> Int -> Int -> Block
clockB start end hh mm =
    let cl_time = t hh mm in
    ClockB { start, end : Just end } $ Clock
            { hour : fromEnum $ T.hour cl_time
            , minute : fromEnum $ T.minute cl_time
            , second : Just $ fromEnum $ T.second cl_time
            }

{-
clockB :: OrgDateTime -> OrgDateTime -> Int -> Int -> Block
clockB start end hh mm =
    para
        [ text "CLOCK: "
        , range
            start
            end
        , text " "
        , clock $ t hh mm
        ] -- FIXME: create a block variation for it
-}


-- | active timestamp with given `Date` and no specific `Time` or repeat / delays
adate :: T.Date -> OrgDateTime
adate date =
    OrgDateTime
        { date
        , time : Nothing
        , active : true
        , delay : Nothing
        , repeat : Nothing
        }


-- | inactive timestamp with given `Date` and no specific `Time` or repeat / delays
idate :: T.Date -> OrgDateTime
idate =
    adate >>> unwrap >>> _ { active = false } >>> wrap


-- | active timestamp with given `Date` and given `Time` and no repeat / delays
adatetime :: T.Date -> T.Time -> OrgDateTime
adatetime date time =
    adate date # at_ time


-- | inactive timestamp with given `Date` and given `Time` and no repeat / delays
idatetime :: T.Date -> T.Time -> OrgDateTime
idatetime date =
    adatetime date >>> unwrap >>> _ { active = false } >>> wrap


-- | change `Time` of the timestamp
at_ :: T.Time -> OrgDateTime -> OrgDateTime
at_ time =
    unwrap
        >>> _ { time = Just $ at_r time }
        >>> wrap


-- | change `Time` of the timestamp to given range
fromto :: T.Time -> T.Time -> OrgDateTime -> OrgDateTime
fromto start end =
    unwrap
        >>> _ { time = Just $ fromto_r start end }
        >>> wrap


-- | change `Dtae` of the timestamp
chdate :: T.Date -> OrgDateTime -> OrgDateTime
chdate date =
    unwrap
        >>> _ { date = date }
        >>> wrap


-- | active timestamp with given `Date` and given `Time` range and no repeat / delays
afromto :: T.Date -> T.Time -> T.Time -> OrgDateTime
afromto date start end =
    adate date # fromto start end


-- | inactive timestamp with given `Date` and given `Time` range and no repeat / delays
ifromto :: T.Date -> T.Time -> T.Time -> OrgDateTime
ifromto date start end =
    idate date # fromto start end


-- | `Words` contructed from this timestamp
at :: OrgDateTime -> Words
at start = DateTime { start, end : Nothing }


-- | `Words` contructed from given timestamp
range :: OrgDateTime -> OrgDateTime -> Words
range start end = DateTime { start, end : Just end }


ch_rng :: (Maybe OrgTimeRange -> OrgTimeRange) -> OrgDateTime -> OrgDateTime
ch_rng rangeF (OrgDateTime rec@{ time }) =
    OrgDateTime $ rec { time = Just $ rangeF time }



-- | Create `Section` of the level `l` with given array of `Words` as its heading and attach given `OrgDoc` to it
sec :: Int -> Array Words -> OrgDoc -> Section
sec level heading doc =
    Section
        { todo : Nothing
        , priority : Nothing
        , cookie : Nothing
        , check : Nothing
        , heading : __neaf (text "") heading
        , level
        , tags : []
        , planning :
            Planning
                { closed : Nothing
                , deadline : Nothing
                , scheduled : Nothing
                , timestamp : Nothing
                }
        , props : Prop.empty
        , logbook : Nothing
        , drawers : []
        , comment : false
        , doc
        }


-- | Create `Section` of the level `l` with given `Words` as its heading and attach given `OrgDoc` to it
sec1 :: Int -> Words -> OrgDoc -> Section
sec1 l = sec l <<< Array.singleton


-- | Create empty `Section` (with empty `OrgDoc` in it) of the level `l` with given array of `Words` as its heading
sece :: Int -> Array Words -> Section
sece l ws = sec l ws emptyDoc


-- | Create empty `Section` (with empty `OrgDoc` in it) of the level `l` with given `Words` as its heading
sece1 :: Int -> Words -> Section
sece1 l = sece l <<< Array.singleton


-- | Create `OrgDoc` with single `Section` only, of the level `l` with given array of `Words` as its heading
ssec :: Int -> Array Words -> OrgDoc -> OrgDoc
ssec level heading doc =
    ds <<< Array.singleton $ sec level heading doc


-- | Create `OrgDoc` with single `Section` only, of the level `l` with given `Words` as its heading
ssec1 :: Int -> Words -> OrgDoc -> OrgDoc
ssec1 l = ssec l <<< Array.singleton


-- | Set heading of the `Section`
sec_head :: Array Words -> Section -> Section
sec_head heading =  __qset _ { heading = __neaf (text "") heading }


-- | Update heading of the `Section`
sec_head' :: (NonEmptyArray Words -> NonEmptyArray Words) -> Section -> Section
sec_head' f (Section sec) = Section $ sec { heading = f sec.heading }


-- | Change heading of the `Section`
sec_head1 :: Words -> Section -> Section
sec_head1 = sec_head <<< Array.singleton


-- | Perform function over the `OrgDoc` inside the section
sec_wdoc :: (OrgDoc -> OrgDoc) -> Section -> Section
sec_wdoc f (Section sec) = Section $ sec { doc = f sec.doc }


set :: Todo -> Section -> Section
set val = __qset _ { todo = Just val }


priority :: Priority -> Section -> Section
priority val = __qset _ { priority = Just val }


low :: Section -> Section
low = identity -- TODO


hi :: Section -> Section
hi = identity -- TODO


cookie :: Cookie -> Section -> Section
cookie val = __qset _ { cookie = Just val }


tag :: String -> Section -> Section
tag s = __qset $ \sec -> sec { tags = s : sec.tags }


untag :: String -> Section -> Section
untag s = __qset $ \sec -> sec { tags = sec.tags # Array.delete s }


level :: Int -> Section -> Section
level val = __qset _ { level = val }


inc :: Section -> Section
inc = __qset $ \sec -> sec { level = min 20 $ sec.level + 1 }


dec :: Section -> Section
dec = __qset $ \sec -> sec { level = max 0 $ sec.level - 1 }


close :: OrgDateTime -> Section -> Section
close dt = __qplan $ _ { closed = Just dt }


deadline :: OrgDateTime -> Section -> Section
deadline dt = __qplan $ _ { deadline = Just dt }


schedule :: OrgDateTime -> Section -> Section
schedule dt = __qplan $ _ { scheduled = Just dt }


timestamp :: OrgDateTime -> Section -> Section
timestamp dt = __qplan $ _ { timestamp = Just dt }


wprop :: OrgProperty String -> Section -> Section
wprop prop = __qset $ \sec -> sec { props = Prop.snoc sec.props prop }


wprops :: Array (OrgProperty String) -> Section -> Section
wprops nextProps = __qset $ \sec -> sec { props = wrap $ unwrap sec.props <> nextProps }


drawer :: String -> Array Words -> Section -> Section
drawer name content = sec_append_drawer $ mk_drawer name content


drawer1 :: String -> Words -> Section -> Section
drawer1 name content = sec_append_drawer $ mk_drawer' name $ NEA.singleton content


mk_drawer :: String -> Array Words -> Drawer
mk_drawer name = mk_drawer' name <<< __neafws


mk_drawer' :: String -> NonEmptyArray Words -> Drawer
mk_drawer' name content = Drawer { name, content }


set_logbook :: LogBook -> Section -> Section
set_logbook logbook (Section sec) = Section $ sec { logbook = Just logbook }



-- | Add words to the drawer
drawer_add :: Array Words -> Drawer -> Drawer
drawer_add nextContent (Drawer { name, content }) = Drawer { name, content : NEA.appendArray content nextContent }


logbook_add :: LogBookEntry -> LogBook -> LogBook
logbook_add logItem (LogBook items) = LogBook $ Array.snoc items logItem


{-
wlast_drawer :: (Drawer -> Drawer) -> Section -> Section
wlast_drawer f (Section sec) =
    Section $ sec { drawers = mapWithIndex checkIndex sec.drawers }
    where
        checkIndex idx drawer | idx == (Array.length sec.drawers - 1) = f drawer
        checkIndex _   drawer | otherwise = drawer


drawer_append :: Array Words -> Section -> Section
drawer_append nextContent =
    wlast_drawer $ \(Drawer { name, content }) -> Drawer { name, content : NEA.appendArray content nextContent }
-}

-- | Append drawer as the last one into the section
sec_append_drawer :: Drawer -> Section -> Section
sec_append_drawer drawer = __qset $ \sec -> sec { drawers = Array.snoc sec.drawers drawer } -- FIXME



note :: Array Words -> OrgDateTime -> LogBookEntry
note text tstamp = LogBookEntry { subject : NoteTaken tstamp, continuation : [ text ] }


comment :: Section -> Section
comment = __qset _ { comment = true }


diary :: String -> Words
diary expr = DiaryW $ Diary { expr, time : Nothing }


diary_r :: String -> OrgTimeRange -> Words
diary_r expr range = DiaryW $ Diary { expr, time : Just range }


-- | create `Time`` range that starts at given time and never ends (it is the same as just stating a time)
at_r :: T.Time -> OrgTimeRange
at_r time = OrgTimeRange { start : time, end : Nothing }


-- | create `Time`` range that starts at given time and ends and given time
fromto_r :: T.Time -> T.Time -> OrgTimeRange
fromto_r start end = OrgTimeRange { start : start, end : Just end }


repeat :: RepeaterMode -> Int -> Interval -> OrgDateTime -> OrgDateTime
repeat mode value interval =
    unwrap
        >>> _ { repeat = Just $
                    wrap { mode, value, interval, with : Nothing }
              }
        >>> wrap


rwith :: Int -> Interval -> OrgDateTime -> OrgDateTime
rwith value interval =
    unwrap
        >>> (\r -> r { repeat = r.repeat <#> updateWith })
        >>> wrap
    where
        updateWith = unwrap >>> _ { with = Just { value, interval } } >>> wrap



delay :: DelayMode -> Int -> Interval -> OrgDateTime -> OrgDateTime
delay mode value interval =
    unwrap
        >>> _ { delay = Just $
                    wrap { mode, value, interval }
              }
        >>> wrap


fn :: String -> Words
fn label = FootnoteRef { label, def : Nothing }


fndef :: String -> String -> Words
fndef label def = FootnoteRef { label, def : Just def }


fndef' :: String -> Words
fndef' def = FootnoteRef { label : "", def : Just def }


fn_ :: String -> Array Words -> Block
fn_ label = Footnote label <<< __neafws


hr :: Block
hr = HRule


fw :: Array Words -> Block
fw = FixedWidth <<< __neafws


kw :: String -> String -> OrgKeyword String
kw = KW.kw


kwopt :: String -> String -> String -> OrgKeyword String
kwopt = KW.kwoptv


with_kw :: String -> String -> Block -> Block
with_kw name value = WithKeyword $ kw name value


with_kws :: Array (OrgKeyword String) -> Block -> Block
with_kws kws block = Array.foldr WithKeyword block kws


lcomment :: Array String -> Block
lcomment = LComment


{-
data At
    = AtMeta String String
    | AtBlock Block
    | AtWords Words
    | AtSection Section
    | AtHeading Words
    | AtProperty String String
    | AtTag String String
    | AtDrawer Drawer
    | AtPriority Priority
    | AtPlanning -- TODO


type Cursor a =
    { path :: Path a
    , parent :: Maybe At
    , current :: At
    }


mapTraverse :: forall a x z. (x -> x -> z) -> (Cursor a -> x) -> x -> OrgFile -> Array z
mapTraverse = ?wh


mapTraverse' :: forall a x z. (x -> x -> z) -> (Cursor a -> x) -> x -> OrgDoc -> Array z
mapTraverse' = ?wh
-}

-- data At :: forall k. (k -> Type) -> k -> Type
data At :: (Type -> Type) -> Type -> Type
data At f a
    = AtBlock Block
    | AtSection Section (f a)


-- traverse ∷ ∀ (x ∷ Type) (b ∷ Type) (a ∷ x) (f ∷ x -> Type). (Array b → Array b → f a) → (At f a → b) → OrgDoc → f a
traverse :: forall b a (f ∷ Type -> Type). Unfoldable f => (f b → f b → f a) -> (At f a -> b) -> OrgDoc -> f a
traverse join f (OrgDoc doc) =
    join (Array.toUnfoldable $ map (f <<< AtBlock) doc.zeroth) (Array.toUnfoldable $ map (f <<< uncurry AtSection <<< deepF) doc.sections)
    where deepF (Section sec) = Section sec /\ traverse join f sec.doc


{-
findBlock :: forall a. BoundedEnum a => OrgFile -> Path a -> Maybe Block
findBlock file path = Nothing


findSection :: forall a. BoundedEnum a => OrgFile -> Path a -> Maybe Section
findSection file path = Nothing


addSection :: forall a. Path a -> OrgFile -> Section -> Path a /\ OrgFile
addSection where_ file _ =
    case where_ of
        Root -> P.root /\ file


-- FIXME: does nothing
-- | add `Block` to the `OrgFile` at given `Path`
addBlock :: forall a. Path a -> OrgFile -> Block -> Path a /\ OrgFile
addBlock where_ file _ = P.root /\ file


addSection' :: forall a. OrgFile -> Section -> Path a /\ OrgFile
addSection' = addSection P.root


addBlock' :: forall a. OrgFile -> Block -> Path a /\ OrgFile
addBlock' = addBlock P.root
-}


-- | update `OrgDoc` inside the `OrgFile` with given function (there's only one root `OrgDoc` inside the file)
wdoc :: (OrgDoc -> OrgDoc) -> OrgFile -> OrgFile
wdoc f (OrgFile { meta, props, doc }) = OrgFile { meta, props, doc : f doc }


-- | add `Section` in front of other child sections in this `OrgDoc`
cons_sec :: Section -> OrgDoc -> OrgDoc
cons_sec sec (OrgDoc { zeroth, sections }) = OrgDoc { zeroth, sections : (sec : sections) }


-- | add `Section` as the last of other child sections in this `OrgDoc`
snoc_sec :: Section -> OrgDoc -> OrgDoc
snoc_sec sec (OrgDoc { zeroth, sections }) = OrgDoc { zeroth, sections : Array.snoc sections sec }


-- | add `Block` in front of other child blocks in this `OrgDoc` in its zeroth section
cons_bl :: Block -> OrgDoc -> OrgDoc
cons_bl bl (OrgDoc { zeroth, sections }) = OrgDoc { zeroth : ( bl : zeroth), sections }


-- | add `Block` as the last of other child blocks in this `OrgDoc` in its zeroth section
snoc_bl :: Block -> OrgDoc -> OrgDoc
snoc_bl bl (OrgDoc { zeroth, sections }) = OrgDoc { zeroth : Array.snoc zeroth bl, sections }


last_bl_of :: OrgDoc -> Maybe Block
last_bl_of (OrgDoc { zeroth, sections }) =
    if Array.length sections > 0 then
        Array.last sections >>= (last_bl_of <<< docs)
    else
        Array.last zeroth


-- | Perform function over the last `Block` of `OrgDoc` when it exists, or leave the document as it is
wlast_bl :: (Block -> Block) -> OrgDoc -> OrgDoc
wlast_bl f (OrgDoc { zeroth, sections }) =
    OrgDoc { zeroth : mapWithIndex checkIndex zeroth, sections }
    where
        checkIndex idx block | idx == (Array.length zeroth - 1) = f block
        checkIndex _   block | otherwise = block


-- | Perform function over the last `Block` of `OrgDoc` when it exists, or else put given block as the first one
wlast_bl' :: (Block -> Block) -> Block -> OrgDoc -> OrgDoc
wlast_bl' f def (OrgDoc { zeroth, sections }) =
    OrgDoc
        { zeroth :
            if Array.length zeroth > 0 then
                mapWithIndex checkIndex zeroth
            else Array.singleton def
        , sections
        }
    where
        checkIndex idx block | idx == (Array.length zeroth - 1) = f block
        checkIndex _   block | otherwise = block


-- | Perform function over the last `Section` of `OrgDoc` when it exists, or leave the document as it is
wlast_sec :: (Section -> Section) -> OrgDoc -> OrgDoc
wlast_sec f (OrgDoc { zeroth, sections }) =
    OrgDoc { zeroth, sections : mapWithIndex checkIndex sections }
    where
        checkIndex idx section | idx == (Array.length sections - 1) = f section
        checkIndex _   section | otherwise = section


-- | Perform function over the last `Section` of `OrgDoc` when it exists, or else put given section as the first one
wlast_sec' :: (Section -> Section) -> Section -> OrgDoc -> OrgDoc
wlast_sec' f def (OrgDoc { zeroth, sections }) =
    OrgDoc
        { zeroth
        , sections :
            if Array.length sections > 0 then
                mapWithIndex checkIndex sections
            else Array.singleton def
        }
    where
        checkIndex idx section | idx == (Array.length sections - 1) = f section
        checkIndex _   section | otherwise = section


-- | _Recursively_ (going into sections, unlike `wlast_bl` and `wlast_bl'`) find the last block and call given function with it; if `OrgDoc` is empty, do nothing
wlast_bl_rec :: (Block -> Block) -> OrgDoc -> OrgDoc
wlast_bl_rec f doc =
    if sectionsn doc > 0 then
        doc # (wlast_sec $ sec_wdoc $ wlast_bl_rec f)
    else
        if blocksn doc > 0 then
            doc # wlast_bl f
        else
            doc


-- | Ensure to append given block to the current end of the root document of the file
append_bl :: Block -> OrgFile -> OrgFile
append_bl = wdoc <<< append_bl'


-- | Ensure to append given block to the end of the given document
append_bl' :: Block -> OrgDoc -> OrgDoc
append_bl' block doc =
    if sectionsn doc > 0 then
        doc # (wlast_sec $ append_bl_sec block)
    else
        if blocksn doc > 0 then
            doc # (wlast_bl $ flip joinB block)
        else
            doc # snoc_bl block


append_bl_sec :: Block -> Section -> Section
append_bl_sec = sec_wdoc <<< snoc_bl


-- | If `Block` can directly contain words (`Of`, `Drawer`, `Footnote`, `DetachedItem`, `Paragraph`, `WithKeyword`, `FixedWidth`, but neither `List` or `LogBook` or `Table` or `HR` or `LComment` or `ClockB`)
-- | add given words to the end of the block
inject_words :: Array Words -> Block -> Block
inject_words words = case _ of
    Of kind curWords -> Of kind $ NEA.appendArray curWords words
    IsDrawer (Drawer { name, content }) ->
        IsDrawer $ Drawer { name, content : NEA.appendArray content words }
    Footnote name curWords -> Footnote name $ NEA.appendArray curWords words
    List list -> List list
    DetachedItem (DetachedListItem def indent props curWords) ->
        DetachedItem $ DetachedListItem def indent props $ NEA.appendArray curWords words
    Table mbFormula table -> Table mbFormula table
    HRule -> HRule
    Paragraph curWords -> Paragraph $ NEA.appendArray curWords words
    WithKeyword kw block -> WithKeyword kw $ inject_words words block
    LComment lines -> LComment lines
    FixedWidth curWords -> FixedWidth $ NEA.appendArray curWords words
    ClockB stend clock -> ClockB stend clock
    JoinB blockA blockB -> JoinB blockA $ inject_words words blockB


det_indent :: String -> DetachedListItem -> DetachedListItem
det_indent indent (DetachedListItem ltype _ props ws) =
    DetachedListItem ltype { mbIndent : Just indent } props ws


det_ltype :: ListType -> DetachedListItem -> DetachedListItem
det_ltype ltype (DetachedListItem _ indent props ws) =
    DetachedListItem ltype indent props ws


det_ch_ltype :: (ListType -> ListType) -> DetachedListItem -> DetachedListItem
det_ch_ltype f (DetachedListItem ltype indent props ws) =
    DetachedListItem (f ltype) indent props ws


det_check :: Check -> DetachedListItem -> DetachedListItem
det_check check (DetachedListItem ltype indent props ws) =
    DetachedListItem ltype indent (props { check = Just check }) ws


det_counter :: Counter -> DetachedListItem -> DetachedListItem
det_counter counter (DetachedListItem ltype indent props ws) =
    DetachedListItem ltype indent (props { counter = Just counter }) ws


det_tag :: String -> DetachedListItem -> DetachedListItem
det_tag tag (DetachedListItem ltype indent props ws) =
    DetachedListItem ltype indent (props { tag = Just tag }) ws


det_drawers :: Array Drawer -> DetachedListItem -> DetachedListItem
det_drawers drawers (DetachedListItem ltype indent props ws) =
    DetachedListItem ltype indent (props { drawers = drawers }) ws


det_add_text :: Array Words -> DetachedListItem -> DetachedListItem
det_add_text words (DetachedListItem ltype indent props curWords) =
    DetachedListItem ltype indent props $ NEA.appendArray curWords words


det_add_drawer :: Drawer -> DetachedListItem -> DetachedListItem
det_add_drawer drawer (DetachedListItem ltype indent props ws) =
    DetachedListItem ltype indent (props { drawers = Array.snoc props.drawers drawer }) ws


isDocEmpty :: OrgDoc -> Boolean
isDocEmpty (OrgDoc { zeroth, sections }) =
    Array.length zeroth == 0 && Array.length sections == 0


parseRepeaterMode :: String -> Maybe RepeaterMode
parseRepeaterMode = case _ of
    "+" -> Just Single
    "++" -> Just FromToday
    ".+" -> Just Jump
    _ -> Nothing


parseDelayMode :: String -> Maybe DelayMode
parseDelayMode = case _ of
    "-" -> Just One
    "--" -> Just All
    _ -> Nothing


parseInterval :: String -> Maybe Interval
parseInterval = case _ of
    "m" -> Just Month
    "y" -> Just Year
    "w" -> Just Week
    "d" -> Just Day
    "h" -> Just Hour
    _ -> Nothing


-- | Parse date from `yyyy-MM-dd` string or init or fill it with zeroes on failure
parseDate :: String -> T.Date
parseDate dateStr =
    case String.split (Pattern "-") dateStr of
        [ yStr, mStr, dStr ] ->
            d
                (fromMaybe 0 $ Int.fromString yStr)
                (fromMaybe 0 $ Int.fromString mStr)
                (fromMaybe 0 $ Int.fromString dStr)
        _ -> d 0 0 0

-- | Parse time from `hh:mm` or `hh:mm:ss` string or fill it with zeroes on failure
parseTime :: String -> T.Time
parseTime timeStr =
    case String.split (Pattern ":") timeStr of
        [ hStr, sStr, xStr ] ->
            t'
                (fromMaybe 0 $ Int.fromString hStr)
                (fromMaybe 0 $ Int.fromString sStr)
                (fromMaybe 0 $ Int.fromString xStr)
        [ hStr, sStr ] ->
            t
                (fromMaybe 0 $ Int.fromString hStr)
                (fromMaybe 0 $ Int.fromString sStr)
        _ -> t 0 0


__items :: ListType -> Array Item -> ListItems
__items lt = ListItems lt <<<  __neaf (item [])


__qset f (Section sec) = Section $ f sec --  unwrap >>> f >> wrap


__qplan ∷ ({ closed ∷ Maybe OrgDateTime , deadline ∷ Maybe OrgDateTime , scheduled ∷ Maybe OrgDateTime , timestamp ∷ Maybe OrgDateTime } → { closed ∷ Maybe OrgDateTime , deadline ∷ Maybe OrgDateTime , scheduled ∷ Maybe OrgDateTime , timestamp ∷ Maybe OrgDateTime } ) → Section → Section
__qplan f =
    __qset $ \sec -> sec { planning = Planning $ f $ case sec.planning of Planning p -> f p }


__neaf def = fromMaybe (NEA.singleton def) <<< NEA.fromArray


__neafws = __neaf $ EmptyW -- FIXME: see Types.importWords
