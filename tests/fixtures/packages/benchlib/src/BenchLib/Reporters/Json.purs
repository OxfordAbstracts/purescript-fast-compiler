module BenchLib.Reporters.Json
  ( Opts
  , codecSuiteResult
  , reportJson
  , reportJson_
  ) where

import Prelude

import BenchLib (BenchResult, CheckResults, GroupResult, Reporter, SampleResult, SuiteResult, CheckResult, defaultReporter)
import Data.Argonaut (stringifyWithIndent)
import Data.Codec.Argonaut (JsonCodec)
import Data.Codec.Argonaut as CA
import Data.Codec.Argonaut.Common as CAC
import Data.Codec.Argonaut.Compat as CAP
import Data.Codec.Argonaut.Record as CAR
import Data.Newtype (unwrap, wrap)
import Data.Profunctor (dimap)
import Data.Time.Duration (Milliseconds)
import Effect.Class (liftEffect)
import Effect.Class.Console as Console
import Node.Encoding (Encoding(..))
import Node.FS.Sync (writeTextFile)
import Node.Path (FilePath)

type Opts =
  { filePath :: FilePath
  , indent :: Int
  }

defaultOpts :: Opts
defaultOpts =
  { filePath: "bench-results.json"
  , indent: 2
  }

reportJson_ :: Reporter
reportJson_ = reportJson identity

reportJson :: (Opts -> Opts) -> Reporter
reportJson mkOpts =
  let
    opts = mkOpts defaultOpts
  in
    defaultReporter
      { onSuiteFinish = \suiteResult -> liftEffect do
          writeTextFile UTF8 opts.filePath $ toJsonStr opts.indent suiteResult
          Console.log ("Wrote JSON report to " <> opts.filePath)
      }

toJsonStr :: Int -> SuiteResult -> String
toJsonStr indent = stringifyWithIndent indent <<< CA.encode codecSuiteResult

--- Codecs ---

codecSuiteResult :: JsonCodec SuiteResult
codecSuiteResult = CAR.object "SuiteResult"
  { suiteName: CA.string
  , groupResults: CA.array codecGroupResult
  }

codecGroupResult :: JsonCodec GroupResult
codecGroupResult = CAR.object "GroupResult"
  { groupName: CA.string
  , benchResults: CA.array codecBenchResult
  , checkResults: CAP.maybe (CA.array codecCheckResults)
  }

codecBenchResult :: JsonCodec BenchResult
codecBenchResult = CAR.object "BenchResult"
  { benchName: CA.string
  , samples: CA.array codecSampleResult
  }

codecCheckResults :: JsonCodec CheckResults
codecCheckResults = CAR.object "CheckResults"
  { success: CA.boolean
  , size: CA.int
  , groupName: CA.string
  , results: CA.array codecCheckResult
  }

codecCheckResult :: JsonCodec CheckResult
codecCheckResult = CAR.object "CheckResult"
  { showedInput: CAC.maybe CA.string
  , showedOutput: CAC.maybe CA.string
  , benchName: CA.string
  }

codecSampleResult :: JsonCodec SampleResult
codecSampleResult = CAR.object "SampleResult"
  { size: CA.int
  , average: codecMilliseconds
  , iterations: CA.int
  }

codecMilliseconds :: JsonCodec Milliseconds
codecMilliseconds = dimap unwrap wrap CA.number