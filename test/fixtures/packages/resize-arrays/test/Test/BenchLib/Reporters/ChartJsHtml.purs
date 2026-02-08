module Test.BenchLib.Reporters.ChartJsHtml
  ( Color
  , LineStyle
  , Opts
  , reportChartJs
  , reportChartJs_
  ) where

import Prelude

import Data.Argonaut as Json
import Data.Codec.Argonaut (JsonCodec)
import Data.Codec.Argonaut as CA
import Data.Codec.Argonaut.Record as CAR
import Data.String (Pattern(..))
import Data.String as Str
import Data.String.Regex as Regex
import Data.String.Regex.Flags (noFlags)
import Data.String.Regex.Unsafe (unsafeRegex)
import Data.Traversable (foldl)
import Effect (Effect)
import Effect.Class.Console as Console
import Node.Encoding (Encoding(..))
import Node.FS.Sync as FS
import Test.BenchLib (Reporter, SuiteResults, defaultReporter)
import Test.BenchLib.Reporters.Json (codecSuiteResults)

type Opts =
  { lineStyles :: Array LineStyle
  , filePath :: String
  }

type LineStyle =
  { color :: Color
  , opacity :: Number
  , width :: Number
  }

type Color =
  { r :: Int
  , g :: Int
  , b :: Int
  }

defaultOpts :: Opts
defaultOpts =
  { lineStyles:
      [ { color: { r: 255, g: 99, b: 132 }, opacity, width }
      , { color: { r: 54, g: 162, b: 235 }, opacity, width }
      , { color: { r: 153, g: 102, b: 255 }, opacity, width }
      , { color: { r: 255, g: 159, b: 64 }, opacity, width }
      , { color: { r: 255, g: 99, b: 132 }, opacity, width }
      , { color: { r: 54, g: 162, b: 235 }, opacity, width }
      , { color: { r: 255, g: 206, b: 86 }, opacity, width }
      , { color: { r: 75, g: 192, b: 192 }, opacity, width }
      , { color: { r: 153, g: 102, b: 255 }, opacity, width }
      , { color: { r: 255, g: 159, b: 64 }, opacity, width }
      ]
  , filePath: "bench-results.html"
  }
  where
  opacity = 0.5
  width = 2.0

writeHtml :: Opts -> SuiteResults -> Effect Unit
writeHtml opts suiteResults = do
  template <- FS.readTextFile UTF8 "test/Test/BenchLib/Reporters/template.html"

  let
    config =
      { lineStyles: opts.lineStyles
      , data: suiteResults
      }

  let jsonStr = Json.stringifyWithIndent 2 $ CA.encode codecConfig config

  let
    replacements =
      [ { regex: unsafeRegex "{{title}}" noFlags
        , replacement: suiteResults.suiteName
        }
      , { regex: unsafeRegex "(/\\* config start \\*/)([\\s\\S]*)(/\\* config end \\*/)" noFlags
        , replacement: "$1\n" <> (indent "      " ("const config = " <> jsonStr)) <> "\n" <> "      $3"
        }
      ]

  let out = foldl (\acc { regex, replacement } -> Regex.replace regex replacement acc) template replacements
  FS.writeTextFile UTF8 opts.filePath out

reportChartJs :: (Opts -> Opts) -> Reporter
reportChartJs mkOpts =
  let
    opts = mkOpts defaultOpts
  in
    defaultReporter
      { onSuiteFinish = \suiteResults -> do
          writeHtml opts suiteResults
          Console.error ("Wrote ChartJS report to " <> opts.filePath)
      }

reportChartJs_ :: Reporter
reportChartJs_ = reportChartJs identity

indent :: String -> String -> String
indent indentStr str = Str.split (Pattern pat) str # map (indentStr <> _) # Str.joinWith pat
  where
  pat = "\n"

type Config =
  { lineStyles :: Array LineStyle
  , data :: SuiteResults
  }

codecConfig :: JsonCodec Config
codecConfig = CAR.object "Config"
  { lineStyles: CA.array codecLineStyle
  , data: codecSuiteResults
  }

codecLineStyle :: JsonCodec LineStyle
codecLineStyle = CAR.object "LineStyle"
  { color: codecColor
  , opacity: CA.number
  , width: CA.number
  }

codecColor :: JsonCodec Color
codecColor = CAR.object "Color"
  { r: CA.int
  , g: CA.int
  , b: CA.int
  }