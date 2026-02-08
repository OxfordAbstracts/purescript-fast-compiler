module Test.Main where

import Prelude

import Data.Array (intercalate)
import Data.Maybe (Maybe(..))
import Data.String (trim)
import Data.String.Regex (replace) as Regex
import Data.String.Regex.Flags (global) as Regex
import Data.String.Regex.Unsafe (unsafeRegex) as Regex
import Effect (Effect)
import Node.ChildProcess.Types (Exit(..), inherit, pipe)
import Node.Encoding (Encoding(..))
import Node.FS.Aff as FS
import Node.Library.Execa (execa)
import Node.Platform (Platform(..))
import Node.Process (platform)
import Test.Spec as Spec
import Test.Spec.Assertions (fail)
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)

main :: Effect Unit
main = runSpecAndExitProcess [consoleReporter] do

  Spec.before_ (nukeLastResults "project") do

    let runTest = runTest' "project"

    Spec.describe "--fail-fast" do
      Spec.it "stops after first failure" do
        runTest ["--fail-fast"] >>= shouldFailWith "fail-fast.txt"

    Spec.describe "--example" do
      Spec.it "can filter by test name" do
        runTest ["--example", "plane"] >>= shouldSucceedWith "filter.txt"

      Spec.it "can filter by test name with spaces in it" do
        runTest ["--example", "gotham city"] >>= shouldFailWith "filter-spaces.txt"

      Spec.it "can filter by FULL test name" do
        runTest ["--example", "gotham city is a dark"] >>= shouldFailWith "filter-full-name.txt"

    Spec.describe "--example-matches" do
      Spec.it "can filter by test name by regex" do
        runTest ["--example-matches", "is\\s(a plane|superman)"] >>= shouldSucceedWith "filter-regex.txt"

      Spec.it "can filter by FULL test name" do
        runTest ["--example-matches", "(metropolis|gotham city)\\sis\\s(superman|time)"] >>= shouldSucceedWith "filter-full-name-regex.txt"

    Spec.describe "--only-failures" do
      Spec.it "runs only tests that failed on last run" do
        runTest [] >>= shouldFail
        runTest ["--only-failures"] >>= shouldFailWith "only-failures.txt"

      Spec.it "runs all tests when there is no last results file" do
        runTest [] >>= shouldFail
        FS.unlink "test-fixtures/project/.spec-results"
        runTest ["--only-failures"] >>= shouldFailWith "only-failures-no-results.txt"

    Spec.describe "--timeout" do
      Spec.it "can set a timeout for the tests" do
        runTest ["--timeout", "1"] >>= shouldFailWith "timeout.txt"

    Spec.describe "--next-failure" do
      Spec.it "runs only tests that failed last time and until first failure" do
        runTest [] >>= shouldFail
        runTest ["--next-failure"] >>= shouldFailWith "next-failure.txt"

    Spec.describe "Combination of several options" do
      Spec.it "can combine --fail-fast with --example" do
        runTest ["--fail-fast", "--example", "bird"] >>= shouldFailWith "fail-fast-and-filter.txt"

      Spec.it "can combine --only-failures with --example-matches and --timeout" do
        runTest ["--timeout", "1"] >>= shouldFail
        runTest ["--only-failures", "--example-matches", "metr.+lis", "--timeout", "1"] >>= shouldFailWith "only-failures-and-filter-regex-and-timeout.txt"


  Spec.describe "#2" do
    let dir = "issue-2-non-identity-generator-monad"
    Spec.before_ (nukeLastResults dir) do
      Spec.it "supports non-Identity test tree generator monad" do
        runTest' dir ["5"] >>= shouldFailWith (dir <> "/5-tests.txt")
        runTest' dir [] >>= shouldFailWith (dir <> "/3-tests.txt")
        runTest' dir ["0"] >>= shouldFailWith (dir <> "/0-tests.txt")

  where
    runTest' dir args' = do
      let opts = _ { cwd = Just $ "test-fixtures/" <> dir, stdin = Just inherit, stdout = Just pipe, stderr = Just pipe }
          args = ["test", "-q", "--"] <> args'
      execa spagoCmd ["build", "-q"] opts >>= _.getResult >>= shouldSucceed
      execa spagoCmd args opts >>= _.getResult

    nukeLastResults dir =
      FS.rm' ("test-fixtures/" <> dir <> "/.spec-results")
        { force: true, maxRetries: 1, recursive: true, retryDelay: 1000 }

    shouldFailWith fixture result =
      case result.exit of
        Normally _ -> checkFixture fixture (stripColors result.stdout)
        _ -> fail $ "Expected command to fail: " <> showResult result

    shouldFail result =
      case result.exit of
        Normally 0 -> fail $ "Expected command to fail: " <> showResult result
        _ -> pure unit

    shouldSucceedWith fixture result =
      case result.exit of
        Normally 0 -> checkFixture fixture (stripColors result.stdout)
        _ -> fail $ "Expected command to succeed: " <> showResult result

    shouldSucceed result =
      case result.exit of
        Normally 0 -> pure unit
        _ -> fail $ "Expected command to succeed: " <> showResult result

    checkFixture fixture actual = do
      expected <- FS.readTextFile UTF8 $ "test-fixtures/" <> fixture
      trim actual `shouldEqualStr` trim expected

    showResult r = intercalate "\n"
      [ "escapedCommand: " <> show r.escapedCommand
      , "canceled: " <> show r.canceled
      , "exit: " <> show r.exit
      , "exitCode: " <> show r.exitCode
      , "signal: " <> show r.signal
      , "signalDescription: " <> show r.signalDescription
      , "pid: " <> show r.pid
      , "killed: " <> show r.killed
      , "timedOut: " <> show r.timedOut
      , "shortMessage: " <> show r.shortMessage
      , "message: " <> show r.message
      , "originalMessage: " <> show r.originalMessage
      , "stdinError: " <> show r.stdinError
      , "stdoutError: " <> show r.stdoutError
      , "stderrError: " <> show r.stderrError
      , "stderr:"
      , r.stderr
      , ""
      , "stdout:"
      , r.stdout
      , ""
      ]

    shouldEqualStr a b =
      when (a /= b) $
        fail $ intercalate "\n"
          [ ""
          , "===== (Actual)"
          , a
          , "====="
          , "  ≠"
          , "===== (Expected)"
          , b
          , "====="
          , ""
          ]

    stripColors = Regex.replace colorRegex ""
    colorRegex = Regex.unsafeRegex "\x1B\\[([0-9]|;)+m" Regex.global

    spagoCmd = case platform of
      Just Win32 -> "spago.ps1"
      _ -> "spago"
