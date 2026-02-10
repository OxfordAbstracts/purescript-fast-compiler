module Test.Spec.Runner.Node where

import Prelude

import Data.Identity (Identity(..))
import Data.Newtype (un)
import Effect (Effect)
import Effect.Aff (Aff, launchAff_)
import Effect.Class (liftEffect)
import Node.Process (exit')
import Test.Spec (SpecT, Spec)
import Test.Spec.Result (Result)
import Test.Spec.Runner (Reporter)
import Test.Spec.Runner as Spec
import Test.Spec.Runner.Node.Config as Cfg
import Test.Spec.Runner.Node.Persist as Persist
import Test.Spec.Summary (successful)
import Test.Spec.Tree (Tree)

-- | Runs the given spec, using configuration derived from CLI options (if any),
-- | and exits the process with an exit indicating success or failure.
-- |
-- | For more control over the configuration or test tree generating monad, use
-- | `runSpecAndExitProcess'`.
runSpecAndExitProcess :: Array Reporter -> Spec Unit -> Effect Unit
runSpecAndExitProcess =
  runSpecAndExitProcess' { defaultConfig: Cfg.defaultConfig, parseCLIOptions: true }

-- | Runs the given spec and exits the process with an exit code indicating
-- | success or failure.
-- |
-- | The `parseCLIOptions` parameter determines whether the `defaultConfig`
-- | should be used as is or CLI options (if any provided) should be applied on
-- | top of it.
-- |
-- | Note that, because this function works for any test tree generator monad
-- | `m`, you will need to specify it somehow. You can either give the spec
-- | parameter an explicit type:
-- |
-- |     spec :: SpecT Aff Unit Aff Unit
-- |     spec = do
-- |       ...
-- |
-- | Or specify the monad via visible type application:
-- |
-- |     runSpecAndExitProcess' @Aff ...
-- |
runSpecAndExitProcess' :: ∀ @m c.
  TestTreeGenerator m
  => { defaultConfig :: Cfg.TestRunConfig' c
     , parseCLIOptions :: Boolean
     }
  -> Array Reporter
  -> SpecT Aff Unit m Unit
  -> Effect Unit
runSpecAndExitProcess' args reporters spec = launchAff_ do
  config <-
    if args.parseCLIOptions then
      Cfg.fromCommandLine' args.defaultConfig Cfg.commandLineOptionParsers
    else
      pure args.defaultConfig
  res <- runSpecAndGetResults config reporters spec
  liftEffect $ exit' $ if successful res then 0 else 1

-- | The core logic of a persistent test run:
-- |
-- |    * Runs the spec tree generation in the given monad `m` (which is usually
-- |      just `Identity`, but can be different in most complex scenarios)
-- |    * Persists results to disk.
-- |    * Returns the tree of results.
-- |
runSpecAndGetResults :: ∀ c m
  . TestTreeGenerator m
  => Cfg.TestRunConfig' c
  -> Array Reporter
  -> SpecT Aff Unit m Unit
  -> Aff (Array (Tree String Void Result))
runSpecAndGetResults config reporters spec = do
  specCfg <- Cfg.toSpecConfig config <#> _ { exit = false }
  results <- generateTestTree $ Spec.evalSpecT specCfg reporters spec
  Persist.persistResults results
  pure results

-- | A monad in which test tree generation happens. This is different from the
-- | monad in which the tests themselves run.
-- |
-- | In most cases the test tree would be generated in `Identity`, making for
-- | deterministic, pure test trees:
-- |
-- |      spec :: SpecT Aff Unit Identity Unit
-- |      spec = do
-- |        it "is a pure test" do
-- |          (2 + 2) `shouldEqual` 4
-- |
-- | But in more complicated scenarios, you might want to generate test trees in
-- | a more powerful monad. For example, the following test tree is generated in
-- | the `Effect` monad, utilizing the effectful function `randomInt` to
-- | determine the number of tests to generate:
-- |
-- |      spec :: SpecT Aff Unit Effect Unit
-- |      spec = do
-- |        numTests <- randomInt 1 10
-- |        for_ numTests \i -> do
-- |          it ("is test number " <> show i) do
-- |            (i + i - i) `shouldEqual` i
-- |
-- | This class assumes that the monad can be evaluated without any additional
-- | parameters. This allows for most normal use cases with ergonomic API. For
-- | more complicated cases, where the generator monad requires something extra
-- | (such as `StateT` or `ReaderT`), you can always use the `mapSpecTree`
-- | function to transform the generated test tree before running it.
class Monad m <= TestTreeGenerator m where
  -- | Evaluates the test tree generator monad, returning the generated test
  -- | tree. See comments on the `TestTreeGenerator` class for more information.
  generateTestTree :: ∀ a. m (Aff a) -> Aff a

instance TestTreeGenerator Identity where
  generateTestTree = un Identity
instance TestTreeGenerator Aff where
  generateTestTree = join
instance TestTreeGenerator Effect where
  generateTestTree = liftEffect >>> join
