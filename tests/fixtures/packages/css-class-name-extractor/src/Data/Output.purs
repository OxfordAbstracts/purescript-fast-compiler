module CssClassNameExtractor.Data.Output where

import Prelude

import CssClassNameExtractor.CssParser (SelectorF(..))
import Data.Array as Array
import Data.Eq.Generic (genericEq)
import Data.Generic.Rep (class Generic)
import Data.Interpolate (i)
import Data.List (List(..))
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)
import Data.String (Pattern(..), Replacement(..), joinWith, replace, toUpper)
import Data.String.CodeUnits (singleton, uncons)
import Node.Path (FilePath, basename, dirname, extname)
import Node.Path as Path

newtype FileBody = FileBody String

coerceFileBody :: FileBody -> String
coerceFileBody (FileBody s) = s

derive instance Generic FileBody _
instance Show FileBody where
  show (FileBody s) = s

instance Eq FileBody where
  eq = genericEq

newtype Namespace = Namespace String

derive instance Generic Namespace _
instance Show Namespace where
  show (Namespace s) = s

instance Eq Namespace where
  eq = genericEq

data Output
  = CssFile
      { namespace :: Namespace
      , body :: FileBody
      , name :: String
      }
  | JsFile
      { path :: FilePath
      , stylePath :: FilePath
      }
  | PursFile
      { namespace :: Namespace
      , path :: FilePath
      , classNames :: List SelectorF
      }

derive instance Generic Output _
instance Show Output where
  show = genericShow

instance Eq Output where
  eq = genericEq

-- | Replacement file extension
-- | ```purescript
-- | > replaceExt foo.js "css"
-- | foo.css
-- | ```
replaceExt :: String -> String -> String
replaceExt path newExt =
  let
    dir = dirname path
    base = basename path
    ext = extname path
    baseWithoutExt = replace (Pattern ext) (Replacement "") base
    newBase = baseWithoutExt <> "." <> newExt
  in
    Path.concat [ dir, newBase ]

-- | Filename head to upper
-- | ```purescript
-- | > capitalizeFilename foo.js
-- | Foo.js
-- | ```
capitalizeFilename :: String -> String
capitalizeFilename path =
  let
    dir = dirname path
    base = basename path
    capitalized = case uncons base of
      Nothing -> base
      Just { head, tail } -> toUpper (singleton head) <> tail
  in
    Path.concat [ dir, capitalized ]

-- | Make a CSS file output
-- | ```purescript run
-- | > makeCssFile (Namespace "Data.Foo.Bar") ".foo { display: flex }" styles.module.css
-- | CssFile { namesapce: Namespace "Data.Foo.Bar", body: ".foo { display: flex }"  }
-- | ```
makeCssFile :: Namespace -> FileBody -> String -> Output
makeCssFile ns fb name = CssFile { namespace: ns, body: fb, name: name }

-- | Make a Js file output
-- | ```purescript run
-- | > makeJsFile "./src/components/styles.css"
-- | JsFile { path ::  "./src/components/Styles.js" } 
-- | ```
makeJsFile :: FilePath -> Output
makeJsFile path = JsFile { path: capitalizeFilename $ replaceExt path "js", stylePath: path }

-- | Make a Purs file output
-- | ```purescript run
-- | > makePursFile (Namespace "Data.Foo.Bar") "./src/components/styles.css" List.fromFoldable [Class "foo"]
-- | PursFile { path ::  "./src/components/Style.purs", namespace: (Namespace "Data.Foo.Bar"), classNames: [Class "foo"] } 
-- | ```
makePursFile :: Namespace -> FilePath -> List SelectorF -> Output
makePursFile namespace path classNames = PursFile { path: capitalizeFilename $ replaceExt path "purs", namespace, classNames }

-- | Convert Output to FileBody. This function extracts the content from CSS files
-- | CSS file -> Extracts the content
-- | JS file -> Generates a JavaScript module that imports and exports CSS modules with a helper function
-- | Purs file -> Generates a PureScript module that exports class names as constants with an FFI helper function
renderOutput :: Output -> FileBody
renderOutput (CssFile { body }) = body
renderOutput (JsFile { stylePath }) = FileBody $ i
  """
import s from "./"""
  fileName
  """"
export const _styles = (name) => s[name]
"""
  where
  fileName :: String
  fileName = basename stylePath

renderOutput (PursFile { classNames, namespace }) =
  FileBody $
    ( """module """ <> (show namespace) <> """ """ <> exports
        <>
          """ where
foreign import _styles :: String -> String
"""
        <> classNameHelpers classNames
    )
  where
  exports :: String
  exports = case classNames of
    Nil -> ""
    classes -> "(" <> (joinedClassNames classes) <> ")"

  className :: SelectorF -> String
  className (Class s) = s
  -- This pattern is unused. Because classNames filtered only Class
  className _ = ""

  classNameArray :: List SelectorF -> Array String
  classNameArray = Array.fromFoldable <<< (map className)

  joinedClassNames :: List SelectorF -> String
  joinedClassNames xs = joinWith "," (classNameArray xs)

  classNameHelper :: SelectorF -> String
  classNameHelper (Class name) = name <> " :: String\n" <> name <> " = " <> "_styles " <> "\"" <> name <> "\""
  classNameHelper _ = ""

  classNameHelpers :: List SelectorF -> String
  classNameHelpers cs = joinWith "\n" (Array.fromFoldable (map classNameHelper cs))

-- | Returns the destination file path for the given output.
-- | The path is determined based on the output type and configuration settings.
getDistPath :: Output -> FilePath
getDistPath (JsFile { path }) = path
getDistPath (CssFile { namespace, name }) = Path.concat [ "output", show namespace, name ]
getDistPath (PursFile { path }) = path

