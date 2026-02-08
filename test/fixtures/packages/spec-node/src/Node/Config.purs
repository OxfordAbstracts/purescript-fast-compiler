module Test.Spec.Runner.Node.Config
  ( OptionParser
  , TestRunConfig
  , TestRunConfig'
  , TestRunConfigRow
  , commandLineOptionParsers
  , defaultConfig
  , fromCommandLine
  , fromCommandLine'
  , toSpecConfig
  )
  where

import Prelude

import Control.Alt ((<|>))
import Control.Alternative (guard)
import Control.Apply (lift2)
import Data.Array (catMaybes, fold, foldl)
import Data.Either (Either(..))
import Data.Int (toNumber)
import Data.Map as Map
import Data.Maybe (Maybe(..), optional)
import Data.Set as Set
import Data.String as Str
import Data.String.Regex (regex, test) as Regex
import Data.String.Regex.Flags (ignoreCase) as Regex
import Data.Time.Duration (Milliseconds(..))
import Data.Traversable (sequence)
import Data.Tuple (fst)
import Data.Tuple.Nested ((/\))
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (class MonadEffect, liftEffect)
import Options.Applicative as Opt
import Partial (crashWith)
import Partial.Unsafe (unsafePartial)
import Test.Spec.Runner (TreeFilter(..))
import Test.Spec.Runner as Spec
import Test.Spec.Runner.Node.Persist (lastPersistedResults)
import Test.Spec.Tree (annotateWithPaths, filterTrees, mapTreeAnnotations, parentSuiteName)

type TestRunConfigRow r =
  ( failFast :: Boolean
  , onlyFailures :: Boolean
  , filter :: Maybe (String -> Boolean)
  , timeout :: Maybe Milliseconds
  | r
  )

type TestRunConfig' r = { | TestRunConfigRow r }
type TestRunConfig = TestRunConfig' ()

-- | A CLI option parser is implemented as a function that _modifies_ the result
-- | rather than returning it. This way we can run multiple parsers in sequence
-- | and accumulate the changes on top of defaults, while keeping the result an
-- | open (extensible) record.
type OptionParser a = Opt.Parser (a -> a)

fromCommandLine :: ∀ m. MonadEffect m => m TestRunConfig
fromCommandLine = fromCommandLine' defaultConfig commandLineOptionParsers

fromCommandLine' :: ∀ m a. MonadEffect m => a -> Array (OptionParser a) -> m a
fromCommandLine' defaultCfg options =
  liftEffect (Opt.customExecParser prefs $ optionParser options) <#>
    \f -> f defaultCfg
  where
    prefs = Opt.defaultPrefs # \(Opt.ParserPrefs p) ->
      Opt.ParserPrefs p { prefShowHelpOnError = true }

defaultConfig :: TestRunConfig
defaultConfig =
  { failFast: false
  , onlyFailures: false
  , filter: Nothing
  , timeout: Just $ Milliseconds 10_000.0
  }

-- | The set of default parsers provided in the box. If you're using your own
-- | parsers for your own CLI options, concatenate them to this array before
-- | passing to `fromCommandLine'`.
commandLineOptionParsers :: ∀ r. Array (OptionParser (TestRunConfig' r))
commandLineOptionParsers =
  [ failFast
  , onlyFailures
  , nextFailure
  , filterByName
  , filterByRegex
  , timeout
  , noTimeout
  ]

-- | Converts the `spec-node` configuration to `spec` configuration. The two are
-- | not the same, because this very conversion is an effectful operation, as,
-- | for example, it depends on the last test run results.
toSpecConfig :: ∀ m r. MonadAff m => TestRunConfig' r -> m Spec.Config
toSpecConfig cfg = do
  filters <- catMaybes <$> sequence [filterToFailures, explicitFilter]
  pure $ Spec.defaultConfig
    { exit = false
    , failFast = cfg.failFast
    , filterTree = filters # foldl combineFilters Spec.defaultConfig.filterTree
    , timeout = cfg.timeout
    }
  where
    explicitFilter = pure $ applyFilter <$> cfg.filter

    filterToFailures
      | cfg.onlyFailures =
          liftAff lastPersistedResults
          <#> Map.filter (not _.success)
          <#> Map.keys
          <#> \names -> do
            guard $ not Set.isEmpty names
            pure $ applyFilter (_ `Set.member` names)

      | otherwise =
          pure Nothing

    applyFilter f = TreeFilter \tests -> tests
      # annotateWithPaths
      # filterTrees (\(name /\ path) _ -> f $ Str.joinWith " " $ parentSuiteName path <> [name])
      <#> mapTreeAnnotations fst

    combineFilters (TreeFilter a) (TreeFilter b) = TreeFilter \tree -> a $ b tree

emptyOptionParser :: ∀ a. OptionParser a
emptyOptionParser = pure identity

combineOptionParsers :: ∀ a. OptionParser a -> OptionParser a -> OptionParser a
combineOptionParsers = lift2 (<<<)

failFastKey = "fail-fast" :: String
onlyFailuresKey = "only-failures" :: String

failFast :: ∀ r. OptionParser { failFast :: Boolean | r }
failFast = ado
  x <- Opt.switch $ fold
    [ Opt.long failFastKey
    , Opt.help "stop the run after first failure"
    ]

  in \r -> r { failFast = r.failFast || x }

onlyFailures :: ∀ r. OptionParser { onlyFailures :: Boolean | r }
onlyFailures = ado
  x <- Opt.switch $ fold
    [ Opt.long onlyFailuresKey
    , Opt.help "run only tests that failed on previous run."
    ]

  in \r -> r { onlyFailures = r.onlyFailures || x }

nextFailure :: ∀ r. OptionParser { failFast :: Boolean, onlyFailures :: Boolean | r }
nextFailure = ado
  x <- Opt.switch $ fold
    [ Opt.short 'n'
    , Opt.long "next-failure"
    , Opt.help $ """
        run only failed tests and stop on first failure.
        Equivalent to --""" <> failFastKey <> " --" <> onlyFailuresKey
    ]

  in \r -> r
    { failFast = r.failFast || x
    , onlyFailures = r.onlyFailures || x
    }

timeout :: ∀ r. OptionParser { timeout :: Maybe Milliseconds | r }
timeout = ado
  seconds <- optional $ Opt.option Opt.int $ fold
    [ Opt.long "timeout"
    , Opt.metavar "SECONDS"
    , Opt.help "timeout for each individual test case, in seconds."
    ]

  let t = seconds <#> \s -> Milliseconds $ toNumber s * 1000.0

  in \r -> r { timeout = t <|> r.timeout }

noTimeout :: ∀ r. OptionParser { timeout :: Maybe Milliseconds | r }
noTimeout = ado
  nt <- Opt.switch $ fold
    [ Opt.long "no-timeout"
    , Opt.help "each individual test case is allowed to run for as long as it wants."
    ]

  in if nt then _ { timeout = Nothing } else identity

filterByName :: ∀ r. OptionParser { filter :: Maybe (String -> Boolean) | r }
filterByName = ado
  pat <- optional $ Opt.strOption $ fold
    [ Opt.long "example"
    , Opt.short 'e'
    , Opt.metavar "TEXT"
    , Opt.help "run only tests whose full names contain the given text. Matching is case-sensitive."
    ]

  let f = pat <#> \s -> Str.toLower >>> Str.contains (Str.Pattern $ Str.toLower s)

  in \r -> r { filter = f <|> r.filter }

filterByRegex :: ∀ r. OptionParser { filter :: Maybe (String -> Boolean) | r }
filterByRegex = ado
  regex <- optional $ Opt.strOption $ fold
    [ Opt.long "example-matches"
    , Opt.short 'E'
    , Opt.metavar "REGEX"
    , Opt.help """
        run only tests whose full names match the given regex.
        This will unapologetically crash if the provided regex doesn't compile.
        The regex is case-insensitive.
      """
    ]

  let f = regex <#> \r ->
            case Regex.regex r Regex.ignoreCase of
              Left err -> unsafePartial $ crashWith $ "Invalid regex: " <> err
              Right regex -> Regex.test regex

  in \r -> r { filter = f <|> r.filter }

optionParser :: ∀ a. Array (OptionParser a) -> Opt.ParserInfo (a -> a)
optionParser options =
  Opt.info (Opt.helper <*> combined) $
    Opt.fullDesc
    <> Opt.header "PureScript Spec test runner for Node"
  where
    combined = foldl combineOptionParsers emptyOptionParser options
