module Data.Text.Doc where

import Prelude

import Data.Array ((:))
import Data.Array (mapWithIndex, intersperse, replicate, uncons, catMaybes, foldl) as Array
import Data.Maybe (Maybe(..))
import Data.String (codePointFromChar, singleton, fromCodePointArray, joinWith) as String
import Data.Foldable (foldl)


data Doc
    = Nil
    | Text String
    | Break
    | Indent
    | Para (Array Doc) -- TODO: merge into `Nest (Maybe Int) (Array Doc)`
    | Nest Int Doc
    | Pair Doc Doc


infixr 6 Nest as :<>


-- TODO: Indent size as an option
-- TODO: Word wrap
-- TODO: `Doc a` with `Value a` constructor


data Break
    = None
    | Space
    -- | WordWrap Int
    | All


data Indent
    = Empty
    | Spaces Int
    | Custom String
    -- | VariableN (Int -> Int) -- take current level of indent and return the required number of indents
    -- | VariableS (Int -> String) -- take current level of indent and return the required string for indentation
    | Tab


renderIndent :: Indent -> String
renderIndent Empty = ""
renderIndent (Spaces n) = String.fromCodePointArray $ Array.replicate n $ String.codePointFromChar ' '
renderIndent (Custom s) = s
renderIndent Tab = String.singleton $ String.codePointFromChar '\t'


renderBreak :: Break -> String
renderBreak None = ""
renderBreak Space = " "
renderBreak All = "\n"


type Options =
    { break :: Break
    , indent :: Indent
    }


type Options' =
    { break :: String
    , indent :: String
    -- , indent :: Int -> String -- could be relative
    }


render' :: Options' -> Int -> Doc -> String
render' opts level = case _ of
    Nil -> ""
    Text s -> s
    Break -> opts.break
    Indent -> opts.indent
    Para docs -> String.joinWith "" $ render' opts 0 <$> Array.intersperse (brIndent level) docs
    Nest n (Para docs) -> String.joinWith "" $ render' opts 0 <$> Array.mapWithIndex (adapt n) docs
    -- Nest _ (Nest m doc) -> render $ Pair (Pair Break $ mkIndent m) doc
    Nest n doc -> render' opts 0 $ adapt n 0 doc
    Pair a b -> render' opts 0 a <> render' opts 0 b
    where
        -- raw :: Doc -> String
        -- raw = render' opts 0 -- fails to run after compilation
        -- adapt n (Nest m x) = Nest (max 0 $ m - n + 1) $ adapt (max 0 $ m - n) x
        adapt _ 0 (Nest m x) = Nest m x
        adapt _ _ (Nest m x) = Pair Break $ Nest m x
        adapt n _ Break = brIndent n
        adapt n 0 doc = Pair (mkIndent n) doc
        adapt n _ doc = Pair (brIndent n) doc
        brIndent = Pair Break <<< mkIndent
        mkIndent 0 = Nil
        mkIndent n = Pair Indent $ mkIndent $ n - 1


makeOpts :: Options -> Options'
makeOpts { break, indent } =
    { break : renderBreak break
    , indent : renderIndent indent
    }


-- render :: Doc -> String
render :: Options -> Doc -> String
render opts = render' (makeOpts opts) 0


instance Semigroup Doc where
    append = Pair


text :: String -> Doc
text = Text
nil :: Doc
nil = Nil
break :: Doc
break = Break
nest :: Int -> Doc -> Doc
nest = Nest
nest' :: Int -> Array Doc -> Doc
nest' i = Nest i <<< Para
stack :: Array Doc -> Doc
stack = Para
concat :: Doc -> Doc -> Doc
concat = Pair
indent :: Doc
indent = Indent


space :: Doc
space = Text " "
mark :: String -> Doc -> Doc
mark s doc = Text s <> space <> doc
bracket :: String -> Doc -> String -> Doc
bracket l x r = bracket' (Text l) x (Text r)
bracket' :: Doc -> Doc -> Doc -> Doc
bracket' l x r = l <> x <> r
wbracket :: String -> String -> Doc -> Doc
wbracket l = flip $ bracket l
wrap :: String -> Doc -> Doc
wrap q = wbracket q q
bracketbr :: String -> Doc -> String -> Doc
bracketbr l x r = bracket l (break <> x <> break) r
wrapbr :: String -> Doc -> Doc
wrapbr q doc = bracketbr q doc q


sp :: Doc -> Doc -> Doc
sp x y = x <> text " " <> y
br :: Doc -> Doc -> Doc
br x y = x <> break <> y
brbr :: Doc -> Doc -> Doc
brbr x y = x <> break <> break <> y
-- spbr :: Doc -> Doc -> Doc
-- spbr x y = x <> (break) <> y
repeat :: Int -> Doc -> Doc
repeat n = foldl (<>) nil <<< Array.replicate n


indentOf :: Int -> Doc
indentOf 0 = nil
indentOf n = indent <> indentOf (n - 1)


indentBy :: Int -> Doc -> Doc
indentBy 0 doc = doc
indentBy n doc = indent <> indentBy (n - 1) doc


infixr 6 sp as <+>
infixr 6 br as </>
infixr 6 brbr as <//>
-- infixr 6 spbr as <+/>


folddoc :: (Doc -> Doc -> Doc) -> Array Doc -> Doc
folddoc f arr =
    case Array.uncons arr of
        Nothing -> nil
        Just { head, tail } ->
            case tail of
                [] -> head
                _ -> f head $ folddoc f tail


spacify :: Array (Maybe Doc) -> Doc
spacify =
    Array.catMaybes
        >>> Array.intersperse space
        >>> join


join :: Array Doc -> Doc
join = Array.foldl (<>) nil


joinWith :: Doc -> Array Doc -> Doc
joinWith bw = Array.intersperse bw >>> join


instance Show Doc where
    show :: Doc -> String
    show = case _ of
        Nil -> "<nil>"
        -- Space -> "<sp>"
        Break -> "<br>"
        Indent -> "<ind>"
        Text str ->
            "<text(" <> str <> ")>"
        Para docs ->
            "<para(" <> (String.joinWith "," $ show <$> docs) <> ")>"
        Pair docA docB ->
            "<concat(" <> show docA <> "," <> show docB <> ")>"
        Nest nextIndent doc ->
            "<nest(" <> show nextIndent <> "," <> show doc <> ")>"