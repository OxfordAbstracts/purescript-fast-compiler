module Test.BenchLib.Reporters.Json
  ( Opts
  , codecSuiteResults
  , reportJson
  , reportJson_
  )
  where

import Prelude

import Data.Argonaut (stringifyWithIndent)
import Data.Codec.Argonaut (JsonCodec)
import Data.Codec.Argonaut as CA
import Data.Codec.Argonaut.Record as CAR
import Data.Newtype (unwrap, wrap)
import Data.Profunctor (dimap)
import Data.Time.Duration (Milliseconds)
import Effect.Class.Console as Console
import Node.Encoding (Encoding(..))
import Node.FS.Sync (writeTextFile)
import Node.Path (FilePath)
import Test.BenchLib (GroupResults, defaultReporter, Reporter, SuiteResults, BenchResult)

type Opts =
  { filePath :: FilePath
  }

defaultOpts :: Opts
defaultOpts = { filePath: "bench-results.json" }

reportJson_ :: Reporter
reportJson_ = reportJson identity

reportJson :: (Opts -> Opts) -> Reporter
reportJson mkOpts =
  let
    opts = mkOpts defaultOpts
  in
    defaultReporter
      { onSuiteFinish = \suiteResults -> do
          writeTextFile UTF8 opts.filePath $ toJsonStr suiteResults
          Console.error ("Wrote JSON report to " <> opts.filePath)
      }

toJsonStr :: SuiteResults -> String
toJsonStr = stringifyWithIndent 2 <<< CA.encode codecSuiteResults

--- Codecs ---

codecSuiteResults :: JsonCodec SuiteResults
codecSuiteResults = CAR.object "SuiteResults"
  { suiteName: CA.string
  , groups: CA.array codecGroupResults
  }

codecGroupResults :: JsonCodec GroupResults
codecGroupResults = CAR.object "GroupResults"
  { groupName: CA.string
  , benchs: CA.array codecBenchResult
  }

codecBenchResult :: JsonCodec BenchResult
codecBenchResult = CAR.object "BenchResult"
  { benchName: CA.string
  , size: CA.int
  , duration: codecMilliseconds
  , iterations: CA.int
  }

codecMilliseconds :: JsonCodec Milliseconds
codecMilliseconds = dimap unwrap wrap CA.number