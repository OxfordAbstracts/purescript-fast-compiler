module BenchLib
  ( Bench
  , BenchOpts
  , BenchResult
  , CheckResult
  , CheckResults
  , Group
  , GroupOpts
  , GroupResult
  , Reporter
  , RunOpts
  , SampleResult
  , Size
  , Suite
  , SuiteOpts
  , SuiteResult
  , basic
  , bench
  , benchAff
  , benchAff_
  , bench_
  , checkAllEq
  , class CanRunOnly
  , defaultReporter
  , group
  , group_
  , normalize
  , normalizeAff
  , normalizeInput
  , normalizeInputAff
  , normalizeOutput
  , normalizeOutputAff
  , only
  , reportConsole
  , runNode
  , runNode_
  , suite
  , suite_
  ) where

import Prelude

import Data.Array (filter, foldr)
import Data.Array as Array
import Data.Array.NonEmpty (NonEmptyArray)
import Data.DateTime.Instant (unInstant)
import Data.Filterable (filterMap)
import Data.Foldable (all)
import Data.Int as Int
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Newtype (unwrap)
import Data.Number.Format as NumFmt
import Data.String as Str
import Data.Time.Duration (Milliseconds(..))
import Data.Traversable (for)
import Data.Tuple.Nested (type (/\), (/\))
import Data.Unfoldable1 (replicate1A)
import Effect (Effect)
import Effect.Aff (Aff, launchAff_)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Class.Console as Console
import Effect.Now (now)
import Effect.Ref as Ref
import Node.Process as Process
import Prim.TypeError (class Warn, Text)

--- Type Aliases

type Size = Int

--- Option Types

-- | Options to run benchmark suites.
type RunOpts =
  { reporters :: Array Reporter
  }

-- | Options for the benchmark suite.
type SuiteOpts =
  { sizes :: Array Size
  , iterations :: Int
  }

-- | Options for the benchmark group.
type GroupOpts a b =
  { sizes :: Array Int
  , iterations :: Int
  , check :: Maybe (Size -> Array (a /\ b) -> Boolean)
  , printInput :: Maybe (a -> String)
  , printOutput :: Maybe (b -> String)
  }

-- | Options for Benchmarks.
type BenchOpts =
  { iterations :: Int
  }

--- Result Types

-- | The result of a benchmark suite.
type SuiteResult =
  { groupResults :: Array GroupResult
  , suiteName :: String
  }

-- | The result of a benchmark group.
type GroupResult =
  { groupName :: String
  , benchResults :: Array BenchResult
  , checkResults :: Maybe (Array CheckResults)
  }

-- | The result of a benchmark.
type BenchResult =
  { benchName :: String
  , samples :: Array SampleResult
  }

-- | The result of one benchmark sample.
type SampleResult =
  { iterations :: Int
  , size :: Size
  , average :: Milliseconds
  }

--- Opaque types

-- | Opaque type for the benchmark suite.
newtype Suite = Suite
  { suiteName :: String
  , runSuite ::
      { iterations :: Int
      , reporter :: Reporter
      , sizes :: Array Size
      }
      -> Aff (Maybe SuiteResult)
  }

-- | Opaque type for the benchmark group.
newtype Group = Group
  { only :: Boolean
  , groupName :: String
  , runGroup ::
      { reporter :: Reporter
      , iterations :: Int
      , sizes :: Array Int
      }
      -> Aff GroupResult
  }

-- | Opaque type for the benchmark.
newtype Bench a b = Bench
  { only :: Boolean
  , benchName :: String
  , runBench ::
      { iterations :: Int
      , size :: Size
      }
      -> Aff { sampleResult :: SampleResult, input :: Aff a, output :: Aff b }
  }

derive instance Functor (Bench a)

--- Reporter types

-- | A reporter is a set of functions that are called at different stages of the benchmark.
-- | It allows to customize the output of the benchmark suite or perform other actions like writing to a file.
type Reporter =
  { onSuiteStart :: String -> Aff Unit
  , onGroupStart :: String -> Aff Unit
  , onBenchStart :: String -> Aff Unit
  , onSampleStart :: Size -> Aff Unit
  , onSampleFinish :: SampleResult -> Aff Unit
  , onBenchFinish :: BenchResult -> Aff Unit
  , onGroupFinish :: GroupResult -> Aff Unit
  , onSuiteFinish :: SuiteResult -> Aff Unit
  }

type CheckResults =
  { groupName :: String
  , success :: Boolean
  , size :: Size
  , results :: Array CheckResult
  }

type CheckResult =
  { showedInput :: Maybe String
  , showedOutput :: Maybe String
  , benchName :: String
  }

--- Internal Types

type BenchName = String

type GroupName = String

--- Running the benchmark suite

-- | Run the benchmark suite.
runNode :: (RunOpts -> RunOpts) -> Suite -> Effect Unit
runNode mkRunOpts (Suite { runSuite }) = launchAff_ do
  let
    { reporters } = mkRunOpts defaultRunOpts

  -- Merge reporters into a single reporter:
  let
    reporter = foldr (<>) defaultReporter reporters

  let { iterations, sizes } = defaultSuiteOpts

  result <- runSuite { reporter, iterations, sizes }

  case result of
    Nothing -> pure unit
    Just _ -> liftEffect $ Process.exit' 1

--- Exported utility functions

-- | Check if all elements in the array are equal.
-- | Useful for checking the results of benchmarks.
checkAllEq :: forall a. Eq a => Array a -> Boolean
checkAllEq items =
  case Array.head items of
    Just x -> Array.all (_ == x) items
    Nothing -> true

--- Defaults

defaultRunOpts :: RunOpts
defaultRunOpts =
  { reporters: [ reportConsole ]
  }

defaultSuiteOpts :: SuiteOpts
defaultSuiteOpts =
  { sizes: [ 0, 25_000, 50_000, 100_000 ]
  , iterations: 1000
  }

mkDefaultGroupOpts :: forall r a b. { sizes :: Array Size, iterations :: Int | r } -> GroupOpts a b
mkDefaultGroupOpts { sizes, iterations } =
  { sizes
  , iterations
  , check: Nothing
  , printInput: Nothing
  , printOutput: Nothing
  }

mkDefaultBenchOpts :: forall r. { iterations :: Int | r } -> BenchOpts
mkDefaultBenchOpts { iterations } =
  { iterations
  }

--- Core functions

-- | Create a benchmark suite of a given name.
-- | The suite will be run with the provided options.
-- | The suite is a collection of groups, each containing multiple benchmarks.
suite :: String -> (SuiteOpts -> SuiteOpts) -> Array Group -> Suite
suite suiteName mkSuiteOpts groups_ = Suite
  { suiteName
  , runSuite: \{ reporter } -> do
      reporter.onSuiteStart suiteName

      let { iterations, sizes } = mkSuiteOpts defaultSuiteOpts
      let groups = mayGetOnlies groups_

      groupResults <- for groups \(Group { runGroup }) ->
        ( do
            groupResult <- runGroup { reporter, iterations, sizes }

            pure groupResult
        )

      let suiteResult = { groupResults, suiteName }

      reporter.onSuiteFinish suiteResult

      pure
        if isSuccess groupResults then
          Nothing
        else
          Just suiteResult
  }

isSuccess :: Array GroupResult -> Boolean
isSuccess groupResults =
  let
    checkResults = groupResults
      # map
          ( \{ checkResults } -> case checkResults of
              Just xs -> xs
              Nothing -> []
          )
      # join

    failures = filter (\{ success } -> not success) checkResults
    nFailures = Array.length failures
  in
    nFailures == 0

type PerSizeItf a b =
  { addEntry :: { size :: Size, benchName :: String, input :: a, output :: b } -> Aff Unit
  , getCheckResults :: Aff (Maybe (Array CheckResults))
  }

mkPerSizeItf :: forall a b. GroupName -> GroupOpts a b -> Aff (PerSizeItf a b)
mkPerSizeItf groupName groupOpts@{ printInput, printOutput } = liftEffect do
  refAccum <- Ref.new (Map.empty :: Map Size (ResultPerSize a b))

  pure
    { addEntry: \{ size, benchName, input, output } -> liftEffect $ Ref.modify_
        ( Map.insertWith (<>) size [ { benchName, input, output } ]
        )
        refAccum

    , getCheckResults: do
        accum <- liftEffect $ Ref.read refAccum

        let
          ret = groupOpts.check # map \checkFn ->
            Map.toUnfoldable accum
              # map
                  ( \(size /\ results_) ->
                      let
                        results = map
                          ( \{ benchName, input, output } ->
                              { benchName
                              , showedInput: map (_ $ input) printInput
                              , showedOutput: map (_ $ output) printOutput
                              }
                          )
                          results_

                        success = checkFn size (map (\{ input, output } -> input /\ output) results_)
                      in
                        { groupName, size, success, results }
                  )

        pure ret
    }

-- | Create a benchmark group of a given name.
-- | The group will be run with the provided options.
-- | The group is a collection of benchmarks
group
  :: forall a b
   . String
  -> (GroupOpts a b -> GroupOpts a b)
  -> Array (Bench a b)
  -> Group
group groupName mkGroupOpts benches_ =
  Group
    { groupName
    , only: false
    , runGroup: \defOpts@{ reporter } -> do
        reporter.onGroupStart groupName

        let
          groupOpts@{ sizes, iterations } = mkGroupOpts $ mkDefaultGroupOpts defOpts

        let benches = mayGetOnlies benches_

        perSizeItf <- mkPerSizeItf groupName groupOpts

        benchResults <- for benches
          ( \(Bench { benchName, runBench }) -> do
              reporter.onBenchStart benchName
              samples <- for sizes
                ( \size -> do
                    reporter.onSampleStart size

                    { sampleResult, output, input } <- runBench { iterations, size }

                    output <- output
                    input <- input

                    perSizeItf.addEntry { size, benchName, output, input }

                    reporter.onSampleFinish sampleResult
                    pure sampleResult
                )

              let benchResult = { benchName, samples }

              reporter.onBenchFinish benchResult
              pure benchResult
          )

        checkResults <- perSizeItf.getCheckResults

        let groupResult = { groupName, benchResults, checkResults }

        reporter.onGroupFinish groupResult

        pure groupResult
    }

benchAff :: forall a b. String -> (BenchOpts -> BenchOpts) -> (Size -> Aff a) -> (a -> Aff b) -> Bench a b
benchAff benchName mkBenchOpts prepareInput benchFn =
  Bench
    { benchName
    , only: false
    , runBench: \defOpts@{ size } -> do

        let { iterations } = mkBenchOpts $ mkDefaultBenchOpts defOpts

        inputs :: NonEmptyArray _ <- replicate1A iterations (prepareInput size)

        duration <- measureTime \_ -> for inputs \input -> benchFn input

        let average = Milliseconds (unwrap duration / Int.toNumber iterations)

        input <- prepareInput size

        output <- benchFn input

        let sampleResult = { size, average, iterations }

        pure { sampleResult, output: pure output, input: pure input }
    }

type ResultPerSize a b = Array
  { input :: a
  , output :: b
  , benchName :: String
  }

-- Normalization

normalizeAff :: forall a a' b b'. (a -> Aff a') -> (b -> Aff b') -> Bench a b -> Bench a' b'
normalizeAff normIn normOut (Bench rec) = Bench $ rec
  { runBench = \opts -> do
      ret@{ input, output } <- rec.runBench opts
      pure $ ret { input = input >>= normIn, output = output >>= normOut }
  }

normalize :: forall a a' b b'. (a -> a') -> (b -> b') -> Bench a b -> Bench a' b'
normalize normIn normOut = normalizeAff (pure <<< normIn) (pure <<< normOut)

normalizeInputAff :: forall a a' b. (a -> Aff a') -> Bench a b -> Bench a' b
normalizeInputAff norm = normalizeAff norm pure

normalizeOutputAff :: forall a b b'. (b -> Aff b') -> Bench a b -> Bench a b'
normalizeOutputAff norm = normalizeAff pure norm

normalizeInput :: forall a a' b. (a -> a') -> Bench a b -> Bench a' b
normalizeInput norm = normalize norm identity

normalizeOutput :: forall a b b'. (b -> b') -> Bench a b -> Bench a b'
normalizeOutput norm = normalize identity norm

basic :: forall a b. Bench a b -> Bench Unit Unit
basic = normalizeAff (const $ pure unit) (const $ pure unit)

--- Typeclasses

-- | A combinator for entities that can be run only once.
-- | This is useful while debugging or developing benchmarks.
-- | So you do not have to run the whole suite again and again.
class CanRunOnly a where
  only :: Warn (Text "`only` usage") => a -> a

instance CanRunOnly (Bench a b) where
  only (Bench rec) = Bench $ rec { only = true }

instance CanRunOnly Group where
  only (Group rec) = Group $ rec { only = true }

class IsOnly a where
  isOnly :: a -> Boolean

instance IsOnly (Bench a b) where
  isOnly (Bench rec) = rec.only

instance IsOnly Group where
  isOnly (Group rec) = rec.only

--- API shortcuts

bench :: forall a b. String -> (BenchOpts -> BenchOpts) -> (Size -> a) -> (a -> b) -> Bench a b
bench name mkOpts prepareFn benchFn = benchAff name mkOpts (pure <<< prepareFn) (pure <<< benchFn)

bench_ :: forall a b. String -> (Size -> a) -> (a -> b) -> Bench a b
bench_ name prepareFn benchFn = bench name identity prepareFn benchFn

-- | Like `benchAff`, but with default options.
benchAff_ :: forall a b. String -> (Size -> Aff a) -> (a -> Aff b) -> Bench a b
benchAff_ name prepareFn benchFn = benchAff name identity prepareFn benchFn

runNode_ :: Suite -> Effect Unit
runNode_ = runNode identity

-- | Like `suite`, but with default options.
suite_ :: String -> Array Group -> Suite
suite_ groupName benchmarks = suite groupName identity benchmarks

-- | Like `group`, but with default options.
group_ :: forall a b. String -> Array (Bench a b) -> Group
group_ groupName benches = group groupName identity benches

--- Utils

mayGetOnlies :: forall a. IsOnly a => Array a -> Array a
mayGetOnlies mayOnlies =
  let
    onlys = filter isOnly mayOnlies
  in
    if Array.null onlys then mayOnlies else onlys

measureTime :: forall a m. MonadEffect m => (Unit -> m a) -> m Milliseconds
measureTime action = do
  startTime <- liftEffect now
  _ <- action unit
  endTime <- liftEffect now
  let duration = unwrap (unInstant endTime) - unwrap (unInstant startTime)
  pure (Milliseconds duration)

asciColorStr :: Int -> String -> String
asciColorStr color str =
  let
    colorCode = "\x1b[" <> show color <> "m"
    resetCode = "\x1b[0m"
  in
    colorCode <> str <> resetCode

bgGray :: Int
bgGray = 100

bold :: Int
bold = 1

-- Reporter

-- | Default reporter useful for selective overriding.
-- | It will do nothing.
defaultReporter :: Reporter
defaultReporter =
  { onSuiteStart: const $ pure unit
  , onGroupStart: const $ pure unit
  , onSampleStart: const $ pure unit
  , onBenchStart: const $ pure unit
  , onSuiteFinish: const $ pure unit
  , onGroupFinish: const $ pure unit
  , onSampleFinish: const $ pure unit
  , onBenchFinish: const $ pure unit
  }

-- | Console reporter.
-- | It will print the results to the console in human readable format.
reportConsole :: Reporter
reportConsole = defaultReporter
  { onSuiteStart = \name -> Console.log
      (asciColorStr bold ("• Suite: " <> name))

  , onGroupStart = \name -> Console.log
      (asciColorStr bold ("  • Group: " <> name))

  , onBenchStart = \benchName -> Console.log
      (asciColorStr bold "    • " <> (asciColorStr bold $ asciColorStr bgGray ("Bench: " <> benchName)))

  , onBenchFinish = \_ -> Console.log ""

  , onGroupFinish = \_ -> Console.log ""

  , onSampleFinish = \{ size, average, iterations } -> Console.log
      ( asciColorStr bold "      • " <> printStats " "
          [ "size" /\ Int.toStringAs Int.decimal size /\ Nothing
          , "count" /\ Int.toStringAs Int.decimal iterations /\ Nothing
          , "avg" /\ printMs average /\ Just "ms"
          ]
      )

  , onSuiteFinish = \suiteResult -> do
      let summary = getSummary suiteResult
      Console.log $ asciColorStr bold "Suite finished"
      Console.log
        ( printStats "\n"
            [ "groups" /\ Int.toStringAs Int.decimal summary.countGroups /\ Nothing
            , "checked" /\ Int.toStringAs Int.decimal summary.countCheckedGroups /\ Nothing
            , "failed" /\ Int.toStringAs Int.decimal summary.countFailedGroups /\ Nothing
            ]
        )
  }

getSummary :: SuiteResult -> Summary
getSummary { groupResults } =
  let
    checkedBenchs = groupResults
      # filterMap (\{ checkResults } -> checkResults)

    failedBenchs = checkedBenchs
      # filter (\results -> all (\{ success } -> not success) results)
  in
    { countGroups: Array.length groupResults
    , countCheckedGroups: Array.length checkedBenchs
    , countFailedGroups: Array.length failedBenchs
    }

type Summary =
  { countGroups :: Int
  , countCheckedGroups :: Int
  , countFailedGroups :: Int
  }

printStats :: String -> Array (String /\ String /\ Maybe String) -> String
printStats sep stats = Str.joinWith sep (map (\(k /\ v /\ un) -> k <> "=" <> asciColorStr bold v <> fromMaybe "" un) stats)

printMs :: Milliseconds -> String
printMs (Milliseconds ms) = NumFmt.toStringWith (NumFmt.fixed 4) ms