module Data.Text.Format.Dodo.Format where

import Prelude

import Color (Color)
import Data.Array (singleton, (:))
import Data.Either (Either(..)) as E
import Data.Either (Either)
import Data.Bounded (top, bottom)
import Data.Enum (class Enum, fromEnum, toEnum, pred, succ)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (class Newtype)
import Data.String (joinWith) as String
import Data.String.CodeUnits (singleton) as String
import Data.Tuple.Nested ((/\), type (/\))
import Data.FunctorWithIndex (mapWithIndex)

import Dodo (Doc, annotate) as Dodo
import Dodo (text, space, break, enclose, foldWith, foldWithSeparator, lines, paragraph, indent) as D


type Tag = DocWithFormat -- it is called `Tag` For backward compatibility


type DocWithFormat = Dodo.Doc Directive


_tag :: Directive -> DocWithFormat -> DocWithFormat
_tag = Dodo.annotate


_etag :: Directive -> DocWithFormat
_etag t = _tag t $ mempty


newtype FootnoteId = FootnoteId (Either Int String)
newtype Anchor = Anchor String
newtype ProgrammingLanguage = ProgrammingLanguage String
newtype Url = Url String
newtype Term = Term DocWithFormat
newtype Definition = Definition DocWithFormat
newtype TermAndDefinition = TAndD (Term /\ Definition)
newtype Caption = Caption String
newtype ImageParams =
        ImageParams
            { width :: ImageSide
            , height :: ImageSide
            , caption :: Caption
            }
newtype QuoteOf = QuoteOf String


derive instance Newtype FootnoteId _
derive instance Newtype Anchor _
derive instance Newtype ProgrammingLanguage _
derive instance Newtype Url _
derive instance Newtype Term _
derive instance Newtype Definition _
derive instance Newtype TermAndDefinition _
derive instance Newtype Caption _
derive instance Newtype ImageParams _
derive instance Newtype QuoteOf _


derive newtype instance Show FootnoteId
derive newtype instance Show Anchor
derive newtype instance Show ProgrammingLanguage
derive newtype instance Show Caption
derive newtype instance Show QuoteOf

derive instance Eq HLevel
derive instance Ord HLevel


data Align
    = Left
    | Right
    | Center


data HLevel
    = H1
    | H2
    | H3
    | H4
    | H5
    | H6


data Format
    = Bold
    | Emphasis -- TODO: Emphasis & Italic could be different i.e. in LaTeX
    | Underline
    | Highlight
    | Blink
    | Inverse
    | Invisible
    | Strikethrough
    | Monospaced
    | Header HLevel (Maybe Anchor)
    | Quote (Maybe QuoteOf)
    | Verbatim
    | Link Url
    | InlineImage ImageParams Url
    | Footnote FootnoteId
    | LinkTo FootnoteId
    | Code ProgrammingLanguage
    | Comment
    | FixedWidth
    | Sub
    | Sup
    | Fg (Either String Color)
    | Bg (Either String Color)
    -- TODO: Resize Smaller / Larger / Scale Number / Exact Px


-- data ListKind
--     = Ordered TheWay
--     | Unordered


data Bullet
    = None
    | Disc
    | Asterisk
    | Dash
    | Num
    | Circle
    | Alpha
    | AlphaInv
    | BCustom String
    -- ..


newtype ChunkId = ChunkId String
newtype ChunkClass = ChunkClass String


data WrapKind
    = Block
    | Inline


data TablePart
    = TRoot
    | THeaderRow
    | THeaderCell
    | THeaderSplit
    | TRow
    | TCell
    | TRowSplit
    | TCellSplit


data ListPart
    = LRoot
    | LHeader
    | LItem Bullet Int


data DefListPart
    = DLRoot
    | DLTerm Int
    | DLDefinition Int


data Directive
    = Format Format
    | Align Align
    | Image ImageParams Url
    | List ListPart
    | DefList DefListPart
    | Table TablePart
    | WithId WrapKind ChunkId
    | WithClass WrapKind ChunkClass
    | Hr
    | Newpage
    | Pagebreak (Maybe Int)
    | Custom String (Array (String /\ String))
    -- TODO: comment block


data ImageSide -- FIXME: reuse some other type
    = Auto
    | Px Int


hr :: DocWithFormat
hr = _etag Hr


nil :: DocWithFormat
nil = mempty


s :: String -> DocWithFormat
s = plain


plain :: String -> DocWithFormat
plain = D.text -- TODO: preprocess for newlines and spaces first?


lefts :: String -> DocWithFormat
lefts = left <<< plain


left :: DocWithFormat -> DocWithFormat
left = _tag $ Align Left


rights :: String -> DocWithFormat
rights = right <<< plain


right :: DocWithFormat -> DocWithFormat
right = _tag $ Align Right


centers :: String -> DocWithFormat
centers = center <<< plain


center :: DocWithFormat -> DocWithFormat
center = _tag $ Align Center


bolds :: String -> DocWithFormat
bolds = bold <<< plain


bold :: DocWithFormat -> DocWithFormat
bold = _tag $ Format Bold


em :: DocWithFormat -> DocWithFormat
em = _tag $ Format Emphasis


i :: DocWithFormat -> DocWithFormat
i = _tag $ Format Emphasis


u :: DocWithFormat -> DocWithFormat
u = _tag $ Format Underline


thru :: DocWithFormat -> DocWithFormat
thru = _tag $ Format Strikethrough


monos :: String -> DocWithFormat
monos = mono <<< plain


mono :: DocWithFormat -> DocWithFormat
mono = _tag $ Format Monospaced


underlines :: String -> DocWithFormat
underlines = underline <<< plain


underline :: DocWithFormat -> DocWithFormat
underline = _tag $ Format Underline


blinks :: String -> DocWithFormat
blinks = blink <<< plain


blink :: DocWithFormat -> DocWithFormat
blink = _tag $ Format Blink


inverses :: String -> DocWithFormat
inverses = inverse <<< plain


inverse :: DocWithFormat -> DocWithFormat
inverse = _tag $ Format Inverse


invisibles :: String -> DocWithFormat
invisibles = invisible <<< plain


invisible :: DocWithFormat -> DocWithFormat
invisible = _tag $ Format Invisible



wrap :: DocWithFormat -> DocWithFormat -> DocWithFormat -> DocWithFormat
wrap = D.enclose


wraps :: String -> String -> DocWithFormat -> DocWithFormat
wraps l r = wrap (plain l) (plain r)


url :: String -> Url
url = Url


link :: Url -> DocWithFormat -> DocWithFormat
link = _tag <<< Format <<< Link


icaption :: String -> Caption
icaption = Caption


auto_ip :: ImageParams
auto_ip = ImageParams { width : Auto, height : Auto, caption : Caption "" }


img :: Url -> DocWithFormat
img = imgp auto_ip


imgc :: Caption -> Url -> DocWithFormat
imgc = imgp <<< cauto


imgp :: ImageParams -> Url -> DocWithFormat
imgp par = _etag <<< Image par


iimg :: Url -> DocWithFormat -> DocWithFormat
iimg = iimgp auto_ip


iimgc :: Caption -> Url -> DocWithFormat -> DocWithFormat
iimgc caption = iimgp $ ImageParams { width : Auto, height : Auto, caption  }


iimgp :: ImageParams -> Url -> DocWithFormat -> DocWithFormat
iimgp par = _tag <<< Format <<< InlineImage par


sized :: { w :: Int, h :: Int } -> ImageParams
sized = csized $ Caption ""


csized :: Caption -> { w :: Int, h :: Int } -> ImageParams
csized caption { w, h } = ImageParams { width : Px w, height : Px h, caption }


cauto :: Caption -> ImageParams
cauto caption = ImageParams { width : Auto, height : Auto, caption }


ftn :: String -> DocWithFormat -> DocWithFormat
ftn = _tag <<< Format <<< Footnote <<< FootnoteId <<< E.Right


ftni :: Int -> DocWithFormat -> DocWithFormat
ftni = _tag <<< Format <<< Footnote <<< FootnoteId <<< E.Left


to_ftn :: String -> DocWithFormat -> DocWithFormat
to_ftn = _tag <<< Format <<< LinkTo <<< FootnoteId <<< E.Right


to_ftni :: Int -> DocWithFormat -> DocWithFormat
to_ftni = _tag <<< Format <<< LinkTo <<< FootnoteId <<< E.Left


h :: Int -> DocWithFormat -> DocWithFormat
h lvl = _tag <<< Format $ Header (hLevelFromInt lvl) Nothing


h' :: Int -> String -> DocWithFormat -> DocWithFormat
h' lvl = _tag <<< Format <<< Header (hLevelFromInt lvl) <<< Just <<< Anchor


h1 = h 1 :: DocWithFormat -> DocWithFormat
h2 = h 2 :: DocWithFormat -> DocWithFormat
h3 = h 3 :: DocWithFormat -> DocWithFormat
h4 = h 4 :: DocWithFormat -> DocWithFormat
h5 = h 5 :: DocWithFormat -> DocWithFormat
h6 = h 6 :: DocWithFormat -> DocWithFormat


h1' = h' 1 :: String -> DocWithFormat -> DocWithFormat
h2' = h' 2 :: String -> DocWithFormat -> DocWithFormat
h3' = h' 3 :: String -> DocWithFormat -> DocWithFormat
h4' = h' 4 :: String -> DocWithFormat -> DocWithFormat
h5' = h' 5 :: String -> DocWithFormat -> DocWithFormat
h6' = h' 6 :: String -> DocWithFormat -> DocWithFormat



define :: String -> DocWithFormat -> DocWithFormat -- FIXME: should it be singleton or helper for constructing lists?
define term def = dl [ TAndD $ Term (plain term) /\ Definition def ]


dt :: DocWithFormat -> DocWithFormat -> TermAndDefinition
dt term def = TAndD $ Term term /\ Definition def


dl :: Array TermAndDefinition -> DocWithFormat
dl items = _tag (DefList DLRoot)
        $ D.lines
        $ (D.foldWith (<>) <$> mapWithIndex defineInList items)
    where
        defineInList idx (TAndD (Term term /\ Definition def)) =
            [ _tag (DefList $ DLTerm idx) term
            , _tag (DefList $ DLDefinition idx) def
            ]


f :: Format -> DocWithFormat -> DocWithFormat
f = _tag <<< Format


none = None :: Bullet
disk = Disc :: Bullet
asterisk = Asterisk :: Bullet
dash = Dash :: Bullet
num = Num :: Bullet
alpha = Alpha :: Bullet
circle = Circle :: Bullet
nalpha = AlphaInv :: Bullet
bcustom = BCustom :: String -> Bullet



list :: DocWithFormat -> Array DocWithFormat -> DocWithFormat
list = listb Dash


list_ :: Array DocWithFormat -> DocWithFormat
list_ = listb_ Dash


listb :: Bullet -> DocWithFormat -> Array DocWithFormat -> DocWithFormat
listb bullet = _list bullet <<< Just


listb_ :: Bullet -> Array DocWithFormat -> DocWithFormat
listb_ bul = _list bul Nothing


_list :: Bullet -> Maybe DocWithFormat -> Array DocWithFormat -> DocWithFormat
_list bullet mbHeader items =
    _tag (List LRoot)
        $ D.lines
        $ case mbHeader of
            Just header ->
                _tag (List LHeader) header
                : mapWithIndex (_tag <<< List <<< LItem bullet) items
            Nothing ->
                mapWithIndex (_tag <<< List <<< LItem bullet) items


stack :: Array DocWithFormat -> DocWithFormat
stack = D.lines


paras :: Array DocWithFormat -> DocWithFormat
paras = D.paragraph -- Or `D.lines`?


fgcs :: Color -> String -> DocWithFormat
fgcs c = fgc c <<< plain


fgc :: Color -> DocWithFormat -> DocWithFormat
fgc = _tag <<< Format <<< Fg <<< E.Right


fgs :: String -> String -> DocWithFormat
fgs cs = fg cs <<< plain


fg :: String -> DocWithFormat -> DocWithFormat
fg = _tag <<< Format <<< Fg <<< E.Left


bgcs :: Color -> String -> DocWithFormat
bgcs c = bgc c <<< plain


bgc :: Color -> DocWithFormat -> DocWithFormat
bgc = _tag <<< Format <<< Bg <<< E.Right


bgs :: String -> String -> DocWithFormat
bgs cs = bg cs <<< plain


bg :: String -> DocWithFormat -> DocWithFormat
bg = _tag <<< Format <<< Bg <<< E.Left


nl :: DocWithFormat
nl = D.break


nest :: Int -> Array DocWithFormat -> DocWithFormat
nest n = indent n <<< D.lines


indent :: Int -> DocWithFormat -> DocWithFormat
indent 0 = identity
indent 1 = D.indent
indent n | n < 0 = identity
indent n | otherwise = indent $ n - 1


group :: Array DocWithFormat -> DocWithFormat
group = D.lines


joinWith :: DocWithFormat -> Array DocWithFormat -> DocWithFormat
joinWith = D.foldWithSeparator


code :: String -> String -> DocWithFormat
code pl = _tag (Format $ Code $ ProgrammingLanguage pl) <<< plain


tableh :: Array DocWithFormat -> Array (Array DocWithFormat) -> DocWithFormat
tableh hcells rows =
    _tag (Table TRoot)
    $ D.lines
        $ ( _tag (Table THeaderRow)
            $ joinWith (_etag $ Table THeaderSplit)
                $ (_tag $ Table THeaderCell)
                <$> hcells
            )
        : (_tag (Table TRow)
            <$> (joinWith (_etag $ Table TCellSplit)
                <<< map (_tag $ Table TCell))
                <$> rows
            )


table :: Array (Array DocWithFormat) -> DocWithFormat
table = tableh []


quote :: DocWithFormat -> DocWithFormat
quote = _tag $ Format $ Quote Nothing


quote_by :: QuoteOf -> DocWithFormat -> DocWithFormat
quote_by = _tag <<< Format <<< Quote <<< Just


of_ :: String -> QuoteOf
of_ = QuoteOf


space :: DocWithFormat
space = D.space


mark :: DocWithFormat -> DocWithFormat -> DocWithFormat
mark m c = m <> space <> c


sub :: DocWithFormat -> DocWithFormat
sub = _tag $ Format $ Sub


sup :: DocWithFormat -> DocWithFormat
sup = _tag $ Format $ Sup


newpage :: DocWithFormat
newpage = _etag Newpage


pagebreak :: DocWithFormat
pagebreak = _etag $ Pagebreak Nothing


pagebreakAt :: Int -> DocWithFormat
pagebreakAt = _etag <<< Pagebreak <<< Just


id :: String -> DocWithFormat -> DocWithFormat
id = _tag <<< WithId Inline <<< ChunkId


_class :: String -> DocWithFormat -> DocWithFormat
_class = _tag <<< WithClass Inline <<< ChunkClass


bl_id :: String -> DocWithFormat -> DocWithFormat
bl_id = _tag <<< WithId Block <<< ChunkId


bl_class :: String -> DocWithFormat -> DocWithFormat
bl_class = _tag <<< WithClass Block <<< ChunkClass


custom :: String -> DocWithFormat -> DocWithFormat
custom name = _tag $ Custom name []


custom_ :: String -> Array (String /\ String) -> DocWithFormat -> DocWithFormat
custom_ name args = _tag $ Custom name args


_null :: DocWithFormat -> DocWithFormat
_null = identity -- to mark some tag with a plan to replace it with another one in future


{-
-- TODO: also convert to tree
traverse :: (DocWithFormat -> DocWithFormat) -> DocWithFormat -> DocWithFormat
traverse f = case _ of
    Format format tag -> f $ Format format $ traverse f tag
    Align align tag -> f $ Align align $ traverse f tag
    Split tagA tagB -> f $ Split (traverse f tagA) (traverse f tagB)
    Pair tagA tagB -> f $ Pair (traverse f tagA) (traverse f tagB)
    Join with tags -> f $ Join (traverse f with) $ traverse f <$> tags
    Wrap tagA tagB tagC -> f $ Wrap (traverse f tagA) (traverse f tagB) (traverse f tagC)
    Para tags -> f $ Para $ traverse f <$> tags
    Nest indent tags -> f $ Nest indent $ traverse f <$> tags
    List bullet hDocWithFormat tags -> f $ List bullet (traverse f hDocWithFormat) $ traverse f <$> tags
    Table headers cells -> f $ Table (traverse f <$> headers) (map (traverse f) <$> cells)
    DefList defs -> f $ DefList $ traverseDef <$> defs
    Image params url -> f $ Image params url
    Plain str -> f $ Plain str
    Newline -> f Newline
    Empty -> f Empty
    Hr -> f Hr
    Newpage -> f Newpage
    Pagebreak n -> f $ Pagebreak n
    WithId wk id tag -> f $ WithId wk id $ traverse f tag
    WithClass wk cl tag -> f $ WithClass wk cl $ traverse f tag
    Custom name args tag -> f $ Custom name args $ f tag
    where
        traverseDef :: TermAndDefinition -> TermAndDefinition
        traverseDef (TAndD (Term termDocWithFormat /\ Definition defDocWithFormat)) =
             TAndD $ Term (traverse f termDocWithFormat) /\ Definition (traverse f defDocWithFormat)



levelUp :: DocWithFormat -> DocWithFormat
levelUp = traverse $ case _ of
    Format (Header level anchor) tag -> Format (Header (fromMaybe top $ succ level) anchor) tag
    tag -> tag


levelDown :: DocWithFormat -> DocWithFormat
levelDown = traverse $ case _ of
    Format (Header level anchor) tag -> Format (Header (fromMaybe bottom $ pred level) anchor) tag
    tag -> tag
-}


-- TODO: indent left / right


blank :: DocWithFormat
blank = nl <> nl


class Formatter a where
    format :: a -> DocWithFormat


instance Formatter DocWithFormat where
    format = identity


bulletPrefix :: Int -> Bullet -> String
bulletPrefix index = case _ of
    None -> ""
    Disc -> "•"
    Asterisk -> "*"
    Dash -> "-"
    Circle -> "o" -- FIXME
    Alpha ->    String.singleton (fromMaybe 'a' $ toEnum $ fromEnum 'a' + index) <> "."
    AlphaInv -> String.singleton (fromMaybe 'z' $ toEnum $ fromEnum 'z' - index) <> "."
    Num ->      String.singleton (fromMaybe '1' $ toEnum $ fromEnum '1' + index) <> "."
    BCustom str -> str


{-
disc	Default value. The marker is a filled circle
armenian	The marker is traditional Armenian numbering
circle	The marker is a circle
cjk-ideographic	The marker is plain ideographic numbers
decimal	The marker is a number
decimal-leading-zero	The marker is a number with leading zeros (01, 02, 03, etc.)
georgian	The marker is traditional Georgian numbering
hebrew	The marker is traditional Hebrew numbering
hiragana	The marker is traditional Hiragana numbering
hiragana-iroha	The marker is traditional Hiragana iroha numbering
katakana	The marker is traditional Katakana numbering
katakana-iroha	The marker is traditional Katakana iroha numbering
lower-alpha	The marker is lower-alpha (a, b, c, d, e, etc.)
lower-greek	The marker is lower-greek
lower-latin	The marker is lower-latin (a, b, c, d, e, etc.)
lower-roman	The marker is lower-roman (i, ii, iii, iv, v, etc.)
none	No marker is shown
square	The marker is a square
upper-alpha	The marker is upper-alpha (A, B, C, D, E, etc.)
upper-greek	The marker is upper-greek
upper-latin	The marker is upper-latin (A, B, C, D, E, etc.)
upper-roman	The marker is upper-roman (I, II, III, IV, V, etc.)
-}


instance Bounded HLevel where
    top = H1
    bottom = H6


instance Enum HLevel where
    succ = case _ of
        H1 -> Nothing
        H2 -> Just H1
        H3 -> Just H2
        H4 -> Just H3
        H5 -> Just H4
        H6 -> Just H5
    pred = case _ of
        H1 -> Just H2
        H2 -> Just H3
        H3 -> Just H4
        H4 -> Just H5
        H5 -> Just H6
        H6 -> Nothing


hLevelToInt :: HLevel -> Int
hLevelToInt = case _ of
    H1 -> 1
    H2 -> 2
    H3 -> 3
    H4 -> 4
    H5 -> 5
    H6 -> 6


hLevelFromInt :: Int -> HLevel
hLevelFromInt = case _ of
    0 -> H1
    1 -> H1
    2 -> H2
    3 -> H3
    4 -> H4
    5 -> H5
    6 -> H6
    n -> if n < 0 then top else bottom


-- TODO: do syntax?

instance Show WrapKind where
    show = case _ of
        Block -> "block"
        Inline -> "inline"



instance Show Directive where
    show = case _ of
        Align align -> wraparg "align" (show align)
        Format format -> case format of
            Fg (E.Left colorStr) -> wraparg "fg" (show colorStr)
            Fg (E.Right color) -> wraparg "fg" (show color)
            Bg (E.Left colorStr) -> wraparg "bg" (show colorStr)
            Bg (E.Right color) -> wraparg "bg" (show color)
            Link (Url url) -> wraparg "link" url
            LinkTo (FootnoteId ftnId) ->
                case ftnId of
                    E.Left ftnIntId -> wraparg "link" $ wrap "ftn#" $ show ftnIntId
                    E.Right ftnStrId -> wraparg "link" $ wrap "ftn" $ ftnStrId
            -- Define (Term term) -> let definition = tag in wraptag2 "def" (show term) $ show definition
            Comment -> just "comment"
            Footnote (FootnoteId ftnId) ->
                case ftnId of
                    E.Left ftnIntId -> wraparg "footnote" ("#" <> show ftnIntId)
                    E.Right ftnStrId -> wraparg "footnote" ftnStrId
            InlineImage imgParams (Url url) -> wraptag2 "image" (show imgParams) $ show url
            _ -> wraparg "format" $ show format
        Hr -> just "hr"
        Newpage -> just "newpage"
        Pagebreak mbPriority -> case mbPriority of
            Just n -> wrap "pagebreak" $ show n
            Nothing -> just "pagebreak"
        Image imgParams (Url url) -> wraptag2 "image" (show imgParams) $ show url
        List bullet -> wraplistarg2 "list" "" ""
        DefList definitions -> just "deflist"
        Table item -> just "table"
        WithId wrapKind (ChunkId chunkId) -> wraptag2 "with-id" (show wrapKind) chunkId
        WithClass wrapKind (ChunkClass chunkClass) -> wraptag2 "with-class" (show wrapKind) chunkClass
        Custom name args -> wraparg "custom" name
        where
            just title = "(" <> title <> ")"
            wrap title v = "(" <> title <> ":" <> v <> ")"
            wraparg title arg = "(" <> title <> "(" <> arg <> ")"
            -- wraparg2 title arg1 arg2 = "(" <> title <> "(" <> arg1 <> "," <> arg2 <> "):" <> v <> ")"
            wraptag2 title tag1 tag2 = "(" <> title <> ":" <> tag1 <> "," <> tag2 <> ")"
            wraplist title vals = "(" <> title <> ":" <> String.joinWith "," vals <> ")"
            wraplistarg title arg vals = "(" <> title <> "(" <> arg <> "):" <> String.joinWith "," vals <> ")"
            wraplistarg2 title arg1 arg2 = "(" <> title <> "(" <> arg1 <> "," <> arg2 <> "))"
            -- tableitems t ts = show t <> ":" <> String.joinWith "," (show <$> ts)


instance Show Align where
    show Left = "left"
    show Right = "right"
    show Center = "center"


instance Show Bullet where
    show None = "none"
    show Disc = "disc"
    show Asterisk = "asterisk"
    show Dash = "dash"
    show Circle = "circle"
    show Alpha = "alpha"
    show AlphaInv = "alphainv"
    show Num = "num"
    show (BCustom str) = "custom:" <> str


instance Show HLevel where
    show = case _ of
        H1 -> "H1"
        H2 -> "H2"
        H3 -> "H3"
        H4 -> "H4"
        H5 -> "H5"
        H6 -> "H6"


instance Show Format where
    show = case _ of
        Bold -> "bold"
        Emphasis -> "emphasis"
        Underline -> "underline"
        Highlight -> "highlight"
        Blink -> "blink"
        Inverse -> "inverse"
        Invisible -> "invisible"
        Strikethrough -> "striked"
        Monospaced -> "mono"
        FixedWidth -> "fixed"
        Quote mbAuthor -> "quote" <> case mbAuthor of
            Just (QuoteOf author) -> "(" <> author <> ")"
            Nothing -> ""
        Sub -> "sub"
        Sup -> "sup"
        Verbatim -> "verbatim"
        Footnote ftnId -> "footnote#" <> show ftnId
        Code lang -> "code:" <> show lang
        Header level anchor -> "header#" <> show level <> case anchor of
                                            Just anchor -> "{" <> show anchor <> "}"
                                            Nothing -> ""
        Link (Url url) -> "link:" <> show url
        InlineImage _ (Url url) -> "inline-image:" <> show url
        LinkTo (FootnoteId ftnId) -> case ftnId of
            E.Left intId -> "footnote:#" <> show intId
            E.Right strId -> "footnote:" <> strId
        Comment -> "comment"
        Fg ecolor ->
            "fg(" <> case ecolor of
                    E.Left colorStr -> show colorStr
                    E.Right color -> show color <> ")"
        Bg ecolor ->
            "bg(" <> case ecolor of
                    E.Left colorStr -> show colorStr
                    E.Right color -> show color <> ")"

{-
instance Show TermAndDefinition where
    show (TAndD (Term term /\ Definition def)) = "(" <> show term <> " :: " <> show def <> ")"
-}


instance Show ImageSide where
    show = case _ of
        Auto -> "auto"
        Px n -> show n <> "px"


instance Show ImageParams where
    show (ImageParams rec) = "{" <> show rec.width <> "x" <> show rec.height <> "," <> show rec.caption <> "}"