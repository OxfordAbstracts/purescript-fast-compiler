module Test.Demo where

import Prelude

import Effect.Console (log) as Console

import Foreign (F)

import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Int as Int
import Data.Array (replicate, catMaybes) as Array
import Data.FunctorWithIndex (mapWithIndex)
import Data.String (Pattern(..))
import Data.String (length, split, drop) as String
import Data.Tuple.Nested ((/\))
import Data.Map (fromFoldable, lookup) as Map

import Control.Alt ((<|>))

import Effect (Effect)
import Effect.Class (class MonadEffect)

import Halogen as H
import Halogen.Aff as HA
import Halogen.HTML as HH
-- import Halogen.HTML.Events as HE
import Halogen.Svg.Elements as HS
import Halogen.Svg.Attributes as HSA
import Halogen.VDom.Driver (runUI)
-- import Halogen.Subscription as HSS
import Halogen.Query.Event (eventListener)

import Type.Proxy (Proxy(..))

import Control.Comonad.Cofree ((:<))

import Yoga.Tree (Tree)
-- import Yoga.Tree as Tree
import Yoga.Tree.Extended ((:<~))
import Yoga.Tree.Extended (leaf) as Tree
import Yoga.Tree.Extended.Path (Path) as Tree
import Yoga.Tree.Extended.Path (fromArray) as Path
import Yoga.Tree.Svg (NodeComponent, component_, all) as YST
import Yoga.Tree.Svg.Render (Modes, RenderConfig, NodeMode(..), EdgeMode(..), SoftLimit(..)) as YST
import Yoga.Tree.Svg.Style (Theme(..), tx, tx2, tx3) as YST
import Yoga.Tree.Svg.SvgItem (class IsTreeItem, class IsSvgTreeItem)
import Yoga.Tree.Svg.SvgItem as YSTI
import Yoga.JSON (class WriteForeign, class ReadForeign, readImpl, writeImpl)

import Web.Event.Event as E
import Web.HTML (window) as Web
import Web.HTML.Window (toEventTarget, innerWidth, innerHeight, location) as Window
import Web.HTML.Location (hash) as Location
-- import Web.UIEvent.KeyboardEvent (KeyboardEvent)
-- import Web.UIEvent.KeyboardEvent as KE
-- import Web.UIEvent.KeyboardEvent.EventTypes as KET


demoTree :: Tree DemoItem
demoTree = lettersNumbers -- myTree, simpleTree, manyItems


main :: Effect Unit
main = HA.runHalogenAff do
  body <- HA.awaitBody
  runUI (component demoTree) unit body


type Slots =
  ( tree :: forall q o. H.Slot q o Unit
  )


type State a =
  { tree :: Tree a
  , window :: Maybe { width :: Number, height :: Number }
  , mbFocus :: Maybe Tree.Path
  , mbChildrenLimit :: Maybe Int
  , mbDepthLimit :: Maybe Int
  , theme :: YST.Theme
  }


_tree  = Proxy :: _ "tree"


data Action
  = Initialize
  | HandleResize
  | HandleHashChange


data DemoItem
  = IntItem Int
  | StrItem String


data Example
  = SimpleTree
  | LettersNumbers
  | ManyItems


ii :: Int -> DemoItem
ii = IntItem


ss :: String -> DemoItem
ss = StrItem


q :: forall n. n -> Tree n
q = Tree.leaf


ch :: forall n. Array n -> Array (Tree n)
ch = map Tree.leaf


{-

1
 11
 12
  121
   1211
   1212
  122
   1221
   1222
   1223
  123
  124
   1241
  125
 13
  131
  132
  133
  134
  135
  136
  137
 14
 15
 16
  161
-}


myTree :: Tree DemoItem
myTree =
  ii 1 :<
    [ q $ ii 11
    , ii 12 :<
      [ ii 121 :< ch [ ii 1211, ii 1212 ]
      , ii 122 :< ch [ ii 1221, ii 1222, ii 1223 ]
      , q $ ii 123
      , ii 124 :< ch [ ii 1241 ]
      , q $ ii 125
      ]
    , ii 13 :< (ch $ ii <$> [ 131, 132, 133, 134, 135, 136, 137 ])
    , q $ ii 14
    , q $ ii 15
    , ii 16 :< ch [ ii 161 ]
    ]


simpleTree :: Tree DemoItem
simpleTree =
  ii 1 :<~
    (ii <$>
      [ 11
      , 12
      , 13
      , 14
      , 15
      ]
    )


manyItems :: Tree DemoItem
manyItems =
  ii 1 :<
    [ ii 500 :<~ (ii <$> (mapWithIndex const $ Array.replicate 500 unit))
    , ii 200 :<~ (ii <$> (mapWithIndex const $ Array.replicate 200 unit))
    , ii 25  :<~ (ii <$> (mapWithIndex const $ Array.replicate  25 unit))
    , ii 30  :<~ (ii <$> (mapWithIndex const $ Array.replicate  30 unit))
    , ii 100 :<~ (ii <$> (mapWithIndex const $ Array.replicate 100 unit))
    ]


lettersNumbers :: Tree DemoItem
lettersNumbers =
  ss "all" :<
    [ ss "numbers" :<~ (ii <$> [ 0, 1, 2, 3, 4, 5, 6, 7, 8, 9 ])
    , ss "a-d"     :< ([ ss "a" :<~ aVars, q $ ss "b", ss "c" :<~ cVars, ss "d" :<~ dVars ])
    , ss "e-j"     :< ([ ss "e" :<~ eVars, q $ ss "f", ss "g" :<~ gVars, ss "h" :<~ hVars, ss "i" :<~ iVars, q $ ss "j" ])
    , ss "k-o"     :< ([ ss "k" :<~ kVars, ss "l" :<~ lVars, q $ ss "m", ss "n" :<~ nVars, ss "o" :<~ oVars ])
    , ss "p-u"     :< ([ q $ ss "p", q $ ss "q", ss "r" :<~ rVars, ss "s" :<~ sVars, ss "t" :<~ tVars, ss "u" :<~ uVars ])
    , ss "v-z"     :< ([ q $ ss "v", ss "w" :<~ wVars, q $ ss "x", ss "y" :<~ yVars, ss "z" :<~ zVars ])
    ]
  where
    aVars = ss <$> [ "à", "á", "â", "ä", "ǎ", "æ", "ã", "å", "ā" ]
    cVars = ss <$> [ "ç", "ć", "č", "ċ" ]
    dVars = ss <$> [ "ď", "ð" ]
    eVars = ss <$> [ "è", "é", "ê", "ë", "ě", "ẽ", "ē", "ė", "ę" ]
    gVars = ss <$> [ "ğ", "ġ" ]
    hVars = ss <$> [ "ħ" ]
    iVars = ss <$> [ "ì", "í", "î", "ï", "ǐ", "ĩ", "ī", "ı", "į" ]
    kVars = ss <$> [ "ķ" ]
    lVars = ss <$> [ "ł", "ļ", "ľ" ]
    nVars = ss <$> [ "ñ", "ń", "ņ", "ň" ]
    oVars = ss <$> [ "ò", "ó", "ô", "ö", "ǒ", "œ", "ø", "õ", "ō" ]
    rVars = ss <$> [ "ř" ]
    sVars = ss <$> [ "ß", "ş", "ș", "ś", "š" ]
    tVars = ss <$> [ "ț", "ť", "þ" ]
    uVars = ss <$> [ "ù", "ú", "û", "ü", "ǔ", "ũ", "ū", "ű", "ů" ]
    wVars = ss <$> [ "ŵ" ]
    yVars = ss <$> [ "ý", "ŷ", "ÿ" ]
    zVars = ss <$> [ "ź", "ž", "ż" ]


instance Show DemoItem where
  show = case _ of
    IntItem n -> show n
    StrItem str -> str
instance IsTreeItem DemoItem where
  default = IntItem $ -1
  _export = show
  _import = Int.fromString >>= maybe (StrItem >>> Just) (\n _ -> Just $ IntItem n)
instance IsSvgTreeItem DemoItem where
  foldLabel = show
  pinnedLine = const show


instance WriteForeign DemoItem where
  writeImpl (IntItem int) = writeImpl int
  writeImpl (StrItem str) = writeImpl str
instance ReadForeign DemoItem where
  readImpl f
    =   ((readImpl f :: F Int)    <#> IntItem)
    <|> ((readImpl f :: F String) <#> StrItem)


config :: forall a. IsSvgTreeItem a => YST.RenderConfig a
config =
  { edgeColor : \theme _ _ _ _ -> YST.tx theme
  , edgeLabel : \_ _ _ _ -> "E"
  , valueLabel : const YSTI.foldLabel
  , valueLabelColor : \theme _ _ -> YST.tx2 theme
  , valueLabelWidth : \path -> String.length <<< config.valueLabel path
  , valueColor : \theme _ _ -> YST.tx3 theme
  , componentSize  : const $ const { width : 200.0, height : 25.0 }
  }


modes :: YST.Modes
modes =
  { nodeMode : YST.NodeWithLabel
  , previewMode : YST.Component -- YST.NodeWithLabel
  , pinMode : YST.NodeWithLabel
  , edgeMode : YST.JustEdge -- EdgeWithLabel
  }


component ∷ ∀ query input output m. MonadEffect m => Tree DemoItem -> H.Component query input output m
component startFromTree =
  H.mkComponent
    { initialState
    , render
    , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , initialize = Just Initialize
      }
    }
  where
  initialState :: input -> State DemoItem
  initialState _ =
    { tree : startFromTree
    , window : Nothing
    , mbFocus : Nothing
    , theme : YST.Light
    , mbDepthLimit : Nothing
    , mbChildrenLimit : Nothing
    }

  defaultSize = { width : 1000.0, height : 1000.0 }

  reduceSize { width, height } = { width : width - 10.0, height : height - 10.0 }

  render :: forall action. State DemoItem -> H.ComponentHTML action Slots m
  render state =
    HH.slot_ _tree unit
      (YST.component_ modes config child)
      { tree : state.tree
      , size : reduceSize $ fromMaybe defaultSize state.window
      , elements : YST.all
      , theme : state.theme
      , depthLimit : maybe YST.Infinite YST.Maximum state.mbDepthLimit
      , childrenLimit : maybe YST.Infinite YST.Maximum state.mbChildrenLimit
      , mbFocus : state.mbFocus
      }

  child :: YST.NodeComponent m DemoItem
  child = H.mkComponent
    { initialState : identity
    , render : childString >>> HH.text >>> pure >>> HS.text [ HSA.fill $ HSA.RGB 0 0 0 ]
    , eval: H.mkEval $ H.defaultEval { handleAction = const $ pure unit }
    }

  childString { path, value } =
    show path <> " // " <> YSTI.foldLabel value

  handleAction = case _ of
    Initialize -> do
      window <- H.liftEffect $ Web.window

      handleAction HandleHashChange
      handleAction HandleResize

      H.subscribe' \_ ->
          eventListener
              (E.EventType "resize")
              (Window.toEventTarget window)
              (E.target >=> (const $ Just HandleResize))

      H.subscribe' \_ ->
          eventListener
              (E.EventType "hashchange")
              (Window.toEventTarget window)
              (E.target >=> (const $ Just HandleHashChange))
    HandleResize -> do
      window    <- H.liftEffect $ Web.window
      newWidth  <- H.liftEffect $ Window.innerWidth window
      newHeight <- H.liftEffect $ Window.innerHeight window
      H.modify_ $ _ { window = Just { width : Int.toNumber newWidth, height : Int.toNumber newHeight } }
    HandleHashChange -> do
      window <- H.liftEffect $ Web.window
      loc    <- H.liftEffect $ Window.location window
      opts   <- H.liftEffect $ Location.hash loc

      let
        optPair = case _ of
          [] -> ("" /\ "")
          [n] -> (n /\ "")
          [n, v] -> (n /\ v)
          [n, v, _] -> (n /\ v)
          _ -> ("" /\ "")
        optsMap = Map.fromFoldable $
          if String.length opts > 0 then
            optPair <$> String.split (Pattern "=") <$> (String.split (Pattern ",") $ String.drop 1 opts)
          else
            []
        example =
          case Map.lookup "ex" optsMap of
            Just "simple" -> simpleTree
            Just "many" -> manyItems
            Just "my" -> myTree
            Just "init" -> myTree
            Just "letnum" -> lettersNumbers
            _ -> lettersNumbers
        mbTheme =
          Map.lookup "theme" optsMap <#> case _ of
            "dark" -> YST.Dark
            "light" -> YST.Light
            _ -> YST.Light
        mbFocus =
          Map.lookup "path" optsMap
            <#> String.split (Pattern "-")
            <#> map Int.fromString
            <#> Array.catMaybes
            <#> Path.fromArray
        mbDepthLimit = Map.lookup "depth" optsMap >>= Int.fromString
        mbChildrenLimit = Map.lookup "children" optsMap >>= Int.fromString

      H.liftEffect $ Console.log opts

      H.modify_ \s -> s
        { tree = example
        , theme = fromMaybe s.theme mbTheme
        , mbFocus = mbFocus
        , mbDepthLimit = mbDepthLimit
        , mbChildrenLimit = mbChildrenLimit
        }
