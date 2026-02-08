module Data.Text.Format.Org.Render where

import Prelude

import Debug as Debug

import Data.Array as Array
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NEA
import Data.Char (fromCharCode)
import Data.Date (Date, day, month, weekday, year)  as DT
import Data.Enum (fromEnum)
import Data.Maybe (Maybe(..), maybe, fromMaybe, isJust)
import Data.Either (Either(..), either)
import Data.Newtype (unwrap)
import Data.String (toUpper, toLower, take, length, trim, toCodePointArray, singleton) as String
import Data.String.CodeUnits (singleton) as SCU
import Data.Time (Time, hour, minute) as DT
import Data.Tuple.Nested ((/\))
import Data.CodePoint.Unicode (isUpper) as UC

import Data.Text.Doc (Doc, (<+>), (</>), (<//>))
import Data.Text.Doc as D

import Data.Text.Format.Org.Construct (isDocEmpty) as Org
import Data.Text.Format.Org.Types (OrgFile(..), OrgDoc(..))
import Data.Text.Format.Org.Types as Org
import Data.Text.Format.Org.Keyword as KW
import Data.Text.Format.Org.Property as Prop

import Data.Text.Output (class ToDoc)
import Data.Time (Time, hour, minute) as DT
import Data.Tuple.Nested ((/\))


newtype Deep = Deep Int


data DrawerMode
    = DrawerUpper
    | DrawerLower
    | KeepCase


layout :: OrgFile -> Doc
layout = layoutWith defaultRO


{- instance ToDoc OrgFile where
    toDoc = layout -}


layoutWith :: RO -> OrgFile -> Doc
layoutWith ro (OrgFile { meta, props, doc }) =
    case (KW.isEmpty meta /\ Prop.isEmpty props /\ Org.isDocEmpty doc) of
        (true /\ true /\ true) -> D.nil
        (false /\ true /\ true) -> renderKWMetaBlock
        (true /\ true /\ false) -> layoutDoc ro root doc
        (false /\ false /\ false) ->
            renderKWMetaBlock
            <//> renderPropsMetaBlock
            <//> layoutDoc ro root doc
        (false /\ false /\ true) ->
            renderKWMetaBlock
            <//> renderPropsMetaBlock
        (false /\ true /\ false) ->
            renderKWMetaBlock
            <//> layoutDoc ro root doc
        (true /\ false /\ true) ->
            renderPropsMetaBlock
        (true /\ false /\ false) ->
            renderPropsMetaBlock
            <//> layoutDoc ro root doc
    where
        renderKWMetaBlock = meta # KW.toJson # unwrap # map (either layoutProperty layoutKeyword) # D.stack
        renderPropsMetaBlock =
            if Prop.hasProperties props then
                props # Prop.toJson # unwrap # map layoutProperty # D.stack
            else D.nil


layoutDoc :: RO -> Deep -> OrgDoc -> Doc
layoutDoc ro deep (OrgDoc { zeroth, sections }) =
    if (not $ Array.length zeroth == 0) then
        renderZerothBlock
        </>
        renderSectionsBlock
    else
        renderSectionsBlock
    where
        renderZerothBlock = zeroth # map (layoutBlock ro deep) # D.joinWith D.break
        renderSectionsBlock = sections # map (layoutSection ro) # D.join


layoutBlock :: RO -> Deep -> Org.Block -> Doc
layoutBlock ro deep = case _ of
    Org.Of conf words ->
        case blockNameAndArgs conf of
            nameDoc /\ mbArgsDoc ->
                let
                    firstLine = D.text "#+BEGIN_" <> nameDoc <> case mbArgsDoc of
                        Just argsDoc -> D.space <> argsDoc
                        Nothing -> D.nil
                    endLine = D.text "#+END_" <> nameDoc
                in D.indentBy indent firstLine
                    </> D.nest' indent (words # NEA.toArray # _splitByBreak)
                    </> D.indentBy indent endLine
    Org.List items ->
        layoutItems ro (Items deep) deep items
    Org.DetachedItem ditem@(Org.DetachedListItem ltype { mbIndent } _ _) ->
        let
            -- deep' = case deep of Deep n -> Deep $ n + maybe 0 String.length mbIndent
            deep' = Deep $ maybe 0 String.length mbIndent
        in
            layoutItems ro (Items deep') deep'
                $ Org.ListItems ltype
                $ NEA.singleton
                $ Org.itemFromDetached ditem
    Org.Table mbFormat rows ->
        layoutTable mbFormat $ NEA.toArray rows
    Org.Paragraph words ->
        words
            # NEA.toArray
            # _splitByBreak
            # D.nest' indent
    Org.HRule ->
        D.text "-----"
    Org.FixedWidth words ->
        words
            # NEA.toArray
            # _splitByBreak' (\ws -> D.text ": " <> layoutWords ws)
            # D.nest' indent
    Org.LComment lines ->
        lines
            # map Org.Plain
            # _splitByBreak' (\ws -> D.text "# " <> layoutWords ws)
            # D.nest' indent
    Org.WithKeyword kwd block ->
        D.nest indent (either layoutProperty layoutKeyword $ KW.toRec kwd)
        </> layoutBlock ro deep block
    Org.JoinB blockA blockB ->
        layoutBlock ro deep blockA </> layoutBlock ro deep blockB
    Org.IsDrawer drawer ->
        layoutDrawer ro (Block deep) deep drawer
    -- Org.IsLogBook logbook ->
    --     layoutLogBook ro (Block deep) deep logbook
    Org.Footnote label def ->
        D.bracket "[" (D.text "fn:" <> D.text label) "]"
            <+> D.stack (layoutWords <$> NEA.toArray def) -- FIXME: impoperly renders line breaks, see 04e
    Org.ClockB { start, end } clock ->
        D.text "CLOCK:" <+>
        case end of
            Just end' -> layoutDateTime start <> D.text "--" <> layoutDateTime end'
            Nothing -> layoutDateTime start
        <+> D.text "=>" <+> layoutClock clock
    -- Quote
    -- const D.nil
    -- where
    --     withIndent lines =
    --         D.nest
    where

        blockNameAndArgs = case _ of
            Org.Quote -> D.text "QUOTE" /\ Nothing
            Org.Example -> D.text "EXAMPLE" /\ Nothing
            Org.Center -> D.text "CENTER" /\ Nothing
            Org.Verse -> D.text "VERSE" /\ Nothing
            Org.Export -> D.text "EXPORT" /\ Nothing
            Org.Comment -> D.text "COMMENT" /\ Nothing
            Org.Code mbLang -> D.text "SRC" /\ (case mbLang of
                    Just (Org.Language lang) -> Just $ D.text lang
                    Nothing -> Nothing)
            Org.Custom name args ->
                D.text name /\ (
                    if (Array.length args > 0)
                        then Just $ D.joinWith D.space $ (D.text <$> args)
                        else Nothing
                )

        indent = ro.calcIndent $ Block deep


layoutSection :: RO -> Org.Section -> Doc
layoutSection ro (Org.Section section) =
    let
        deep = deepAs section.level
        headingLines = section.heading # NEA.toArray # _splitByBreak
        headingFirstLine = Array.head headingLines
        headingHasSeveralLines = Array.length headingLines > 1
        restOfHeadingLines = Array.tail headingLines # fromMaybe []
        -- headingText =
        --     section.heading # NEA.toArray # map layoutWords # D.join
        levelPrefix = Array.replicate section.level "*" # Array.fold # D.text
        commentPrefix = if section.comment then Just $ D.text "COMMENT" else Nothing
        todoPrefix = section.todo
                        <#> renderTodo
                        <#> D.text
        priorityPrefix = section.priority
                        <#> case _ of
                            Org.Alpha c -> "[#" <> String.toUpper (SCU.singleton c) <> "]"
                            Org.Num n -> "[#" <> show n <> "]"
                        <#> D.text
        cookieSuffix = section.cookie
                        <#> case _ of
                            Org.Split -> "[/]"
                            Org.Percent -> "[%]"
                            Org.Pie -> "[o]"
                        <#> D.text
        tagsSuffix = if Array.length section.tags > 0 then
                        Just $ D.join $ D.text <$> [":"] <> Array.intersperse ":" section.tags <> [":"]
                     else Nothing
        headlingLineCombined =
            [ Just levelPrefix
            , todoPrefix
            , priorityPrefix
            , commentPrefix
            , headingFirstLine
            , cookieSuffix
            , tagsSuffix
            ]
            # D.spacify
        planningItem tag datetime = D.text (String.toUpper tag) <> D.text ":" <+> layoutDateTime datetime
        planning =
            unwrap section.planning
        hasPlanning
            =  isJust planning.scheduled
            || isJust planning.deadline
            || isJust planning.timestamp
            || isJust planning.closed
        hasProperties =
            Prop.hasProperties section.props
        propertiesDrawer =
            section.props
                # Prop.toJson
                # unwrap
                # map layoutProperty
                # layoutDrawer' ro (Section deep) deep "PROPERTIES"
        hasLogbookEntries =
            section.logbook # maybe false (unwrap >>> Array.length >>> (_ > 0))
        logbookDrawer logbook =
            layoutLogBook ro (Block deep) deep logbook
        hasOtherDrawers =
            Array.length section.drawers > 0
        otherDrawers =
            section.drawers
                # map (layoutDrawer ro (Section deep) deep)
                # D.joinWith D.break
        planningLine =
            [ planningItem "TIMESTAMP" <$> planning.timestamp
            , planningItem "DEADLINE"  <$> planning.deadline
            , planningItem "SCHEDULED" <$> planning.scheduled
            , planningItem "CLOSED"    <$> planning.closed
            ]
            # D.spacify
        indent = ro.calcIndent $ Section deep
    in
        if not $ Org.isDocEmpty section.doc then
            headlingLineCombined
                <> (if hasPlanning then D.break <> planningLine <> D.break else D.break)
                <> (if hasProperties then propertiesDrawer <> D.break else D.nil)
                <> (if hasLogbookEntries then maybe D.nil logbookDrawer section.logbook <> D.break else D.nil)
                <> (if headingHasSeveralLines then D.nest' indent restOfHeadingLines <> D.break else D.nil)
                <> (if hasOtherDrawers then otherDrawers <> D.break else D.nil)
                <> layoutDoc ro deep section.doc
        else
            headlingLineCombined
            <> (if hasProperties then D.break <> propertiesDrawer <> D.break else D.nil)
            <> (if hasLogbookEntries then maybe D.nil logbookDrawer section.logbook <> D.break else D.nil)
            <> (if headingHasSeveralLines then D.nest' indent restOfHeadingLines <> D.break else D.nil)
            <> (if hasOtherDrawers then otherDrawers <> D.break else D.nil)
            <> (if hasPlanning then D.break <> planningLine <> D.break else D.break)


layoutWords :: Org.Words -> Doc
layoutWords = case _ of
    Org.Plain plain -> D.text plain
    Org.Marked mk s ->
        markWith mk $ D.text s
    Org.Break -> D.break
    Org.Link trg mbText ->
        case mbText of
            Just text ->
                D.bracket
                    "["
                    (D.concat (D.bracket "[" (linkTrg trg) "]")
                              (D.bracket "[" (D.text text) "]")
                    )
                    "]"
            Nothing ->
                D.bracket "[[" (linkTrg trg) "]]"
    Org.RawLink trg ->
        linkTrg trg
    Org.Image src ->
        D.bracket "[[" (imgSrc src) "]]"
    Org.RawImage src ->
        imgSrc src
    Org.Punct p -> D.text $ String.singleton p -- FIXME
    Org.Markup str -> D.text str -- FIXME
    Org.DateTime { start, end } ->
        case end of
            Just end' -> layoutDateTime start <> D.text "--" <> layoutDateTime end'
            Nothing -> layoutDateTime start
    Org.ClockW (Org.Clock clock) -> D.text "=>" <+> layoutClock (Org.Clock clock)
    Org.DiaryW (Org.Diary diary) ->
        D.bracket "<%%"
            (D.text diary.expr <> case diary.time of
                Just range -> D.space <> layoutRange range
                Nothing -> D.nil
            )
        ">"
    Org.FootnoteRef { label, def } ->
        D.bracket "["
            (D.text "fn:" <> D.text label <> case def of
                Just def' -> D.text ":" <> D.text def'
                Nothing -> D.nil
            )
        "]"
    Org.JoinW wa wb -> layoutWords wa <> layoutWords wb
    Org.Entity entity -> D.text "\\" <> D.text entity
    Org.EmptyW -> D.nil
    where
        markWith mk doc = case mk of
            Org.Bold -> D.wrap "*" doc
            Org.Italic -> D.wrap "/" doc
            Org.Underline -> D.wrap "_" doc
            Org.Strike -> D.wrap "+" doc
            Org.InlineCode -> D.wrap "~" doc
            Org.Verbatim -> D.wrap "=" doc
            Org.Highlight -> D.wrap "^^" doc
            Org.Subscript -> D.text "_" <> doc
            Org.Superscript -> D.text "^" <> doc
            Org.Error -> D.wrap "X" doc
            Org.Inline key -> D.bracket ("@@" <> inlineKey key <> ":") doc "@@"
            Org.And mka mkb -> markWith mkb $ markWith mka doc
        linkTrg = case _ of
            Org.Remote url -> D.text url
            Org.Local url -> D.text "file:" <> D.text url
            Org.Heading trg -> D.text trg
        imgSrc = case _ of
            Org.RemoteSrc url -> D.text url
            Org.LocalSrc url -> D.text "file:" <> D.text url
        inlineKey = case _ of
            Org.IHtml -> "html"
            Org.IComment -> "comment"


layoutDateTime :: Org.OrgDateTime -> Doc
layoutDateTime =
    case _ of
        Org.OrgDateTime
            { active, date, time, repeat, delay } ->
                let
                    datetime_ =
                        [ Just $ layoutDate date
                        , layoutRange <$> time
                        , layoutRepeater <$> repeat
                        , layoutDelay <$> delay
                        ]
                        # D.spacify
                in if active then
                    D.bracket "<" datetime_ ">"
                else
                    D.bracket "[" datetime_ "]"
    where
        interval = case _ of
            Org.Hour -> "h"
            Org.Day -> "d"
            Org.Week -> "w"
            Org.Month -> "m"
            Org.Year -> "y"
        rmode = case _ of
            Org.Single -> "+"
            Org.FromToday -> "++"
            Org.Jump -> ".+"
        dmode = case _ of
            Org.One -> "-"
            Org.All -> "--"
        layoutRepeater = case _ of
            Org.Repeater r ->
                rmode r.mode <> show r.value <> interval r.interval <>
                    case r.with of
                        Just w -> "/" <> show w.value <> interval w.interval
                        Nothing -> ""
            >>> D.text
        layoutDelay = case _ of
            Org.Delay d ->
                dmode d.mode <> show d.value <> interval d.interval
            >>> D.text


layoutClock :: Org.Clock -> Doc
layoutClock (Org.Clock c) =
    D.text (showdd $ c.hour) <> D.text ":" <>
    D.text (showdd $ c.minute)


layoutDate :: DT.Date -> Doc
layoutDate d =
    D.text (show $ fromEnum $ DT.year d) <> D.text "-" <>
    D.text (showdd $ fromEnum $ DT.month d) <> D.text "-" <>
    D.text (showdd $ fromEnum $ DT.day d) <+>
    D.text (showwd $ DT.weekday d)
    where
        showwd = String.take 3 <<< show


layoutTime :: DT.Time -> Doc
layoutTime t =
    D.text (showdd $ fromEnum $ DT.hour t) <> D.text ":" <>
    D.text (showdd $ fromEnum $ DT.minute t)


layoutRange :: Org.OrgTimeRange -> Doc
layoutRange = case _ of
    Org.OrgTimeRange { start, end } ->
        layoutTime start <> case end of
            Just end' -> D.text "-" <> layoutTime end'
            Nothing -> D.nil


layoutItems :: RO -> IndentSubject -> Deep -> Org.ListItems -> Doc
layoutItems ro parentSubj deep (Org.ListItems lt items) = layoutItemsWith ro parentSubj deep lt items


layoutItemsWith :: RO -> IndentSubject -> Deep -> Org.ListType -> NonEmptyArray Org.Item -> Doc
layoutItemsWith ro parentSubj (Deep deep) lt items  =
    let
        markerPrefix idx = case lt of
            Org.Bulleted -> "*"
            Org.Plussed -> "+"
            Org.Hyphened -> "-"
            Org.Numbered -> show (idx + 1) <> "."
            Org.NumberedFrom n -> show (idx + n) <> "."
            Org.Alphed -> (fromMaybe "?" $ SCU.singleton <$> (fromCharCode $ 0x61 + idx)) <> "."
            Org.Prefixed str -> str
            # D.text
        checkPrefix = case _ of
            Org.Uncheck -> "[ ]"
            Org.Halfcheck -> "[-]"
            Org.Check -> "[X]"
            >>> D.text
        counterPrefix (Org.Counter n) =
            D.text $ "[@" <> show n <> "]"
        tagPrefix tag =
            D.text $ tag <> " ::"
        itemText ws =
            ws # NEA.toArray # map layoutWords # D.join
        indentSubjFor = ListItem parentSubj lt
        indentFor = ro.calcIndent <<< indentSubjFor
        itemLine idx (Org.Item opts ws Nothing) =
            [ Just $ markerPrefix idx
            , opts.check <#> checkPrefix
            , opts.counter <#> counterPrefix
            , opts.tag <#> tagPrefix
            , Just $ itemText ws
            ]
            # D.spacify
            # D.indentBy (indentFor idx)
        itemLine idx (Org.Item opts ws (Just subs)) =
            let
                item = (Org.Item opts ws Nothing)
                indentSubj = indentSubjFor idx
                curIndent = indentFor idx
                nextDeep = deepAs curIndent
            in
                itemLine idx item
                </> layoutItems ro indentSubj nextDeep subs
        itemMaybeWithDrawers idx item@(Org.Item opts _ _) =
            itemLine idx item
            <> if hasDrawers opts then D.break <> drawers idx opts else D.nil
        hasDrawers opts =
            Array.length opts.drawers > 0
        drawers idx opts =
            opts.drawers
                # map (layoutDrawer ro (indentSubjFor idx) $ Deep deep)
                # D.joinWith D.break
        indent = deep
        -- indent = ro.calcIndent parentSubj
        --     case parentSubj of
        --         Just subj -> ro.calcIndent subj
        --         Nothing -> ro.calcIndent $ Items deep
    in
        -- D.stack $ NEA.toArray $ NEA.mapWithIndex itemMaybeWithDrawers items
        D.nest' indent $ NEA.toArray $ NEA.mapWithIndex itemMaybeWithDrawers items


layoutProperty :: Prop.JsonPropertyRec String -> Doc
layoutProperty prop =
    let propName = if not prop.append then D.text prop.name else D.text prop.name <> D.text "+"
    in case prop.value of
        Just value ->
            D.wrap ":" propName <+> D.text value
        Nothing ->
            D.wrap ":" propName


layoutKeyword :: KW.JsonKeywordRec String -> Doc
layoutKeyword kwd =
    case kwd.default /\ kwd.value of
            Just optVal /\ Nothing -> D.bracket "#+" (D.text kwd.name <> D.bracket "[" (D.text optVal) "]") ":"
            Just optVal /\ Just value -> D.bracket "#+" (D.text kwd.name <> D.bracket "[" (D.text optVal) "]") ":" <+> D.text value
            Nothing /\ Just value ->  D.bracket "#+" (D.text kwd.name) ":" <+> D.text value
            Nothing /\ Nothing -> D.bracket "#+" (D.text kwd.name) ":"


layoutDrawer :: RO -> IndentSubject -> Deep -> Org.Drawer -> Doc
layoutDrawer ro is deep (Org.Drawer { name, content }) =
    content
        # NEA.toArray
        # _splitByBreak
        # layoutDrawer' ro is deep name


layoutLogBook :: RO -> IndentSubject -> Deep -> Org.LogBook -> Doc
layoutLogBook ro is deep (Org.LogBook entries) =
    entries
        # map layoutLogBookEntry
        # layoutDrawer' ro is deep "LOGBOOK"


layoutDrawer' :: RO -> IndentSubject -> Deep -> String -> Array Doc -> Doc
layoutDrawer' ro is deep name content =
    D.indentBy indent (D.wrap ":" $ D.text $ applyMode name)
    </> D.nest' indent content
    </> D.indentBy indent (D.wrap ":" $ D.text $ applyMode endWord)
    where
        endWord = if Array.all UC.isUpper $ String.toCodePointArray name then "END" else "end"
        indent = ro.calcIndent $ Drawer is deep
        applyMode =
            case ro.drawerPolicy of
                DrawerUpper -> String.toUpper
                DrawerLower -> String.toLower
                KeepCase -> identity


layoutLogBookEntry :: Org.LogBookEntry -> Doc
layoutLogBookEntry (Org.LogBookEntry { subject, continuation }) =
    D.mark "-" $ D.join (subjectText subject)
    <> mbContPostfix
    <>  if Array.length continuation > 0 then
            D.join (D.join <$> map layoutWords <$> continuation)
        else D.nil
    where
      mbContPostfix = if Array.length continuation > 0 then D.text " \\\\" else D.nil
      subjectText = case _ of
        Org.StateChange from to tstamp ->
            [ D.text "State \""
            , D.text $ renderTodo from
            , D.text "\" from \""
            , D.text $ renderTodo to
            , D.text "\" "
            , layoutDateTime tstamp ]
        Org.Reschedule fromts tots -> [ D.text "Rescheduled from \"", layoutDateTime fromts, D.text "\" on \"", layoutDateTime tots, D.text "\"" ]
        Org.NoteTaken tstamp -> [ D.text "Note taken on ", layoutDateTime tstamp ]
        Org.Other words timestamps -> [ D.join $ layoutWords <$> words, D.join $ layoutDateTime <$> timestamps ]


layoutTable :: Maybe Org.TableFormat -> Array Org.TableRow -> Doc
layoutTable mbFormat rows =
    (D.joinWith D.break $ layoutRow <$> rows)
    <> case mbFormat of
        Just (Org.TableFormat format) -> D.break <> D.text "#+TBLFM: " <> D.text format <> D.break
        Nothing -> D.nil
    where
        columnsCount = Array.foldl max 0 $ columnsAt <$> rows
        columnsAt (Org.BreakT _) = 0
        columnsAt (Org.Row columns) = NEA.length columns
        layoutRow (Org.BreakT Nothing) =
            D.wrap "|" $ D.joinWith (D.text "+") $ Array.replicate columnsCount $ D.text "-"
        layoutRow (Org.BreakT (Just (Org.TableCustomBreak customBreak))) =
            D.text customBreak
        layoutRow (Org.Row columns) =
            D.wrap "|" $ D.joinWith (D.text "|") $ layoutColumn <$> NEA.toArray columns
        layoutColumn Org.Empty =
            D.text " "
        layoutColumn (Org.Column words) =
            D.join $ layoutWords <$> NEA.toArray words


showdd ∷ Int → String
showdd n =
    if n < 10 then "0" <> show n else show n


indentByDeep :: RO
indentByDeep =
    { calcIndent : indentFn
    , drawerPolicy : KeepCase
    }
    where
        indentFn (Block deep) = deepToIndent deep
        indentFn (Section deep) = deepToIndent deep
        indentFn (Items deep) = deepToIndent deep
        indentFn (Drawer (ListItem _ parentLt parentIdx) deep) =
            deepToIndent deep + _indentByLt parentIdx parentLt
        indentFn (Drawer _ deep) =
            deepToIndent deep
        indentFn (ListItem parent@(ListItem _ parentLt parentIdx) _ _) =
            indentFn parent + _indentByLt parentIdx parentLt
        indentFn (ListItem parent _ _) =
            indentFn parent


_indentByLt :: Int -> Org.ListType -> Int
_indentByLt idx =
    case _ of
        Org.Bulleted -> 2
        Org.Plussed -> 2
        Org.Hyphened -> 2
        Org.Numbered -> if (idx + 1) < 10 then 3 else 4
        Org.NumberedFrom n -> if (idx + n) < 10 then 3 else 4
        Org.Alphed -> 3
        Org.Prefixed str -> String.length str -- TODO: check


alwaysZeroRO :: RO
alwaysZeroRO =
    { calcIndent : const 0
    , drawerPolicy : KeepCase
    }


defaultRO :: RO
defaultRO =
    { calcIndent : indentFn
    , drawerPolicy : KeepCase
    }
    where
        indentFn (ListItem parent lt idx) =
            case lt of
                Org.Bulleted ->
                    indentFn parent + 2
                _ ->
                    case parent of
                        (ListItem _ parentLt _) ->
                            if (parentLt == lt || parentLt == Org.Bulleted) then
                                indentFn parent + _indentByLt idx lt
                            else 0
                        _ -> 0
        indentFn _ = 0


renderTodo :: Org.Todo -> String
renderTodo = case _ of
    Org.Todo -> "TODO"
    Org.Doing -> "DOING"
    Org.Done -> "DONE"
    Org.Now -> "NOW"
    Org.Next -> "NEXT"
    Org.CustomKW s -> s


_splitByBreak :: Array Org.Words -> Array Doc
_splitByBreak = _splitByBreak' layoutWords


_splitByBreak' :: (Org.Words -> Doc) -> Array Org.Words -> Array Doc
_splitByBreak' process =
    helper >>> map (map process) >>> map D.join
    where
        helper =
            Array.foldl
                (\{ prev, last } w ->
                    case w of
                        Org.Break ->
                            { prev : Array.snoc prev last
                            , last : []
                            }
                        _ ->
                            { prev
                            , last : Array.snoc last w
                            }
                )
                { prev : ([] :: Array (Array Org.Words))
                , last : ([] :: Array Org.Words)
                }
            >>> \{ prev, last } -> Array.snoc prev last


data IndentSubject
    = Block Deep
    | Section Deep
    | Items Deep
    | Drawer IndentSubject Deep -- TODO: consider including parent
    | ListItem IndentSubject Org.ListType Int


type IndentFn = IndentSubject -> Int


type RenderOptions =
    { calcIndent :: IndentFn
    , drawerPolicy :: DrawerMode
    }


type RO = RenderOptions


root :: Deep
root = Deep 0


deepAs :: Int -> Deep
deepAs = Deep


deeper :: Deep -> Deep
deeper = incDeep 1


incDeep :: Int -> Deep -> Deep
incDeep m (Deep n) = Deep $ n + m


deepToIndent :: Deep -> Int
deepToIndent (Deep 0) = 0
deepToIndent (Deep 1) = 2
deepToIndent (Deep n) = 1 + n -- in spaces
