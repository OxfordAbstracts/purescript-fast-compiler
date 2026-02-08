-- | This module defines the random generator monad using a linear congruential
-- | generator, as well as helper funtions for constructing random generators.
-- |
-- | Depending on your underlying monad, stack-safety can be an issue.
-- | All functions (e.g. `vectorOf`) that do not end with `'` are stack-safe,
-- | but sometimes this safety is guaranteed via `MonadRec`.
-- |
-- | If your underlying monad (e.g. `Aff`) is already stack-safe, you can omit
-- | this extra constraint and use the variant that ends with `'`
-- | (e.g. `vectorOf'`).
module Control.Monad.Gen.Trans
  ( GenState
  , GenT(..)
  , runGenT
  , runGenT'
  , withGenT
  , mapGenT
  , execGenT
  , evalGenT
  , perturbGenT
  , resizeGenT
  , Gen
  , runGen
  , withGen
  , mapGen
  , execGen
  , evalGen
  , perturbGen
  , resizeGen
  , repeatable
  , stateful
  , variant
  , suchThat
  , suchThat'
  , sized
  , choose
  , chooseInt
  , oneOf
  , frequency
  , arrayOf
  , arrayOf'
  , arrayOf1
  , arrayOf1'
  , enum
  , listOf
  , listOf'
  , vectorOf
  , vectorOf'
  , elements
  , shuffle
  , shuffle'
  , uniform
  , sample
  , sample'
  , randomSample1
  , randomSampleN
  , randomSampleN'
  ) where

import Prelude

import Control.Alt (class Alt)
import Control.Lazy (class Lazy)
import Control.Monad.Gen.Class (class MonadGen)
import Control.Monad.Rec.Class (class MonadRec, Step(..), tailRecM)
import Control.Monad.State (evalState, execState, mapState, modify_, runState, withState)
import Control.Monad.State.Class (state)
import Control.Monad.State.Trans (StateT(..), evalStateT, execStateT, mapStateT, runStateT, withStateT)
import Data.Array ((:), length, zip, sortBy)
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NEA
import Data.Enum (class BoundedEnum, fromEnum, toEnum)
import Data.Identity (Identity)
import Data.Int (toNumber, floor)
import Data.List (List(..), toUnfoldable)
import Data.Maybe (Maybe(..), fromJust)
import Data.Monoid.Additive (Additive(..))
import Data.Newtype (unwrap)
import Data.Number ((%))
import Data.Semigroup.Foldable (foldMap1)
import Data.Tuple (Tuple(..), fst, snd)
import Effect.Class (class MonadEffect, liftEffect)
import Partial.Unsafe (unsafePartial)
import Random.LCG (Seed, lcgPerturb, lcgM, lcgNext, unSeed, randomSeed)

-- | The state of the random generator monad
-- |
-- | ## The `size` label
-- |
-- | Tests are parameterized by the `size` of the randomly-generated data,
-- | the meaning of which depends on the particular generator used.
type GenState = { newSeed :: Seed, size :: Int }

-- | The random generator monad
-- |
-- | `GenT` is a state monad which encodes a linear congruential generator.
newtype GenT m a = GenT (StateT GenState m a)

derive newtype instance Functor m => Functor (GenT m)
derive newtype instance Monad m => Apply (GenT m)
derive newtype instance Monad m => Applicative (GenT m)
derive newtype instance Monad m => Bind (GenT m)
derive newtype instance Monad m => Monad (GenT m)
derive newtype instance (Monad m, Alt m) => Alt (GenT m)
derive newtype instance MonadRec m => MonadRec (GenT m)
derive newtype instance Lazy (m a) => Lazy (GenT m a)

instance Monad m => MonadGen (GenT m) where
  chooseInt = chooseInt
  chooseFloat = choose
  chooseBool = (_ < 0.5) <$> uniform
  resize f g = sized \s -> resizeGenT (f s) g
  sized = sized

-- | Exposes the underlying function.
runGenT :: forall m a. GenT m a -> GenState -> m (Tuple a GenState)
runGenT gen s = runStateT (runGenT' gen) s

-- | Exposes the underlying `StateT` implementation.
runGenT' :: forall m a. GenT m a -> StateT GenState m a
runGenT' (GenT st) = st

-- | Modify the final state in a `GenT` monad action.
withGenT :: forall m a. (GenState -> GenState) -> GenT m a -> GenT m a
withGenT f = GenT <<< withStateT f <<< runGenT'

-- | Change the type of the result in a `GenT` action
mapGenT :: forall m1 m2 a b. (m1 (Tuple a GenState) -> m2 (Tuple b GenState)) -> GenT m1 a -> GenT m2 b
mapGenT f = GenT <<< mapStateT f <<< runGenT'

-- | Run a random generator, keeping only the generator state.
execGenT :: forall m a. Functor m => GenT m a -> GenState -> m GenState
execGenT = execStateT <<< runGenT'

-- | Run a random generator, keeping only the randomly-generated result
evalGenT :: forall m a. Functor m => GenT m a -> GenState -> m a
evalGenT = evalStateT <<< runGenT'

-- | Perturb a random generator by modifying the current seed
perturbGenT :: forall m a. Monad m => Number -> GenT m a -> GenT m a
perturbGenT n gen = GenT do
  modify_ \s -> s { newSeed = lcgPerturb (float32ToInt32 n) s.newSeed }
  runGenT' gen

-- | Modify a random generator by setting a new size parameter.
resizeGenT :: forall m a. Monad m => Int -> GenT m a -> GenT m a
resizeGenT sz g = GenT $ StateT \{ newSeed, size } ->
  (map _ { size = size }) <$> runGenT g { newSeed, size: sz }

type Gen a = GenT Identity a

-- | Run a random generator
runGen :: forall a. Gen a -> GenState -> Tuple a GenState
runGen = runState <<< runGenT'

-- | Modify the final state in a `Gen` action.
withGen :: forall a. (GenState -> GenState) -> Gen a -> Gen a
withGen f = GenT <<< withState f <<< runGenT'

-- | Change the type of the result in a `Gen` action
mapGen :: forall a b. (Tuple a GenState -> Tuple b GenState) -> Gen a -> Gen b
mapGen f = GenT <<< mapState f <<< runGenT'

-- | Run a random generator, keeping only the generator state.
execGen :: forall a. Gen a -> GenState -> GenState
execGen = execState <<< runGenT'

-- | Run a random generator, keeping only the randomly-generated result
evalGen :: forall a. Gen a -> GenState -> a
evalGen = evalState <<< runGenT'

-- | Perturb a random generator by modifying the current seed
perturbGen :: forall m a. Monad m => Number -> Gen a -> Gen a
perturbGen = perturbGenT

-- | Modify a random generator by setting a new size parameter.
resizeGen :: forall a. Int -> Gen a -> Gen a
resizeGen = resizeGenT

-- | Create a random generator for a function type.
-- | Note that the `a -> Gen b` cannot run effects.
repeatable :: forall m a b. Monad m => (a -> Gen b) -> GenT m (a -> b)
repeatable f = GenT $ StateT \s ->
  pure $ Tuple (\a -> evalGen (f a) s) (s { newSeed = lcgNext s.newSeed })

-- | Create a random generator which uses the generator state explicitly.
stateful :: forall m a. (GenState -> GenT m a) -> GenT m a
stateful f = GenT $ StateT \s -> runGenT (f s) s

-- | Modify a random generator by setting a new random seed.
variant :: forall m a. Seed -> GenT m a -> GenT m a
variant n g = GenT $ StateT \s -> runGenT g s { newSeed = n }

-- | Ensure that a generator only produces values that match a predicate. If
-- | the predicate always returns false the generator will loop forever.
-- | Stack-safety is guaranteed via the `MonadRec` constraint
suchThat :: forall m a. MonadRec m => GenT m a -> (a -> Boolean) -> GenT m a
suchThat gen pred = tailRecM go unit
  where
  go :: Unit -> GenT m (Step Unit a)
  go _ = do
    a <- gen
    pure if pred a then Done a else Loop unit

-- | Ensure that a generator only produces values that match a predicate. If
-- | the predicate always returns false the generator will loop forever.
-- | This is only stack-safe if the underlying monad is stack-safe.
suchThat' :: forall m a. Monad m => GenT m a -> (a -> Boolean) -> GenT m a
suchThat' gen pred = go
  where
  go :: GenT m a
  go = do
    a <- gen
    if pred a then pure a else go

-- | Create a random generator which depends on the size parameter.
sized :: forall m a. (Int -> GenT m a) -> GenT m a
sized f = stateful (\s -> f s.size)

-- | Create a random generator which samples a range of `Number`s i
-- | with uniform probability.
choose :: forall m. Monad m => Number -> Number -> GenT m Number
choose a b = (*) (max' - min') >>> (+) min' >>> unscale <$> uniform
  where
  unscale = (_ * 2.0)
  scale = (_ * 0.5)
  min' = scale $ min a b
  max' = scale $ max a b

-- | Create a random generator which chooses uniformly distributed
-- | integers from the closed interval `[a, b]`.
-- | Note that very large intervals will cause a loss of uniformity.
chooseInt :: forall m. Monad m => Int -> Int -> GenT m Int
chooseInt a b = if a <= b then chooseInt' a b else chooseInt' b a

-- guaranteed a <= b
chooseInt' :: forall m. Monad m => Int -> Int -> GenT m Int
chooseInt' a b = floor <<< clamp <$> choose32BitPosNumber
  where
  choose32BitPosNumber :: GenT m Number
  choose32BitPosNumber =
    (+) <$> choose31BitPosNumber <*> (((*) 2.0) <$> choose31BitPosNumber)

  choose31BitPosNumber :: GenT m Number
  choose31BitPosNumber = toNumber <$> lcgStep

  clamp :: Number -> Number
  clamp x = numA + (x % (numB - numA + one))

  numA = toNumber a
  numB = toNumber b

-- | Create a random generator which selects and executes a random generator from
-- | a non-empty array of random generators with uniform probability.
oneOf :: forall m a. Monad m => NonEmptyArray (GenT m a) -> GenT m a
oneOf xs = do
  n <- chooseInt zero (NEA.length xs - one)
  unsafePartial $ NEA.unsafeIndex xs n

-- | Create a random generator which selects and executes a random generator from
-- | a non-empty, weighted list of random generators.
frequency :: forall m a. Monad m => NonEmptyArray (Tuple Number (GenT m a)) -> GenT m a
frequency xxs = do
  let
    default = snd $ NEA.head xxs
    total = unwrap $ foldMap1 (Additive <<< fst) xxs
    pick i n = case NEA.index xxs i of
      Nothing -> default
      Just (Tuple k x')
        | n <= k -> x'
        | otherwise -> pick (i + 1) (n - k)
  n <- choose zero total
  pick 0 n

-- | Create a random generator which generates an array of random values.
-- | Stack-safety is guaranteed via the `MonadRec` constraint
arrayOf :: forall m a. MonadRec m => GenT m a -> GenT m (Array a)
arrayOf g = sized $ \n -> do
  k <- chooseInt zero n
  vectorOf k g

-- | Create a random generator which generates an array of random values.
-- | This is only stack-safe if the underlying monad is stack-safe.
arrayOf' :: forall m a. Monad m => GenT m a -> GenT m (Array a)
arrayOf' g = sized $ \n -> do
  k <- chooseInt zero n
  vectorOf' k g

-- | Create a random generator which generates a non-empty array of random values.
-- | Stack-safety is guaranteed via the `MonadRec` constraint
arrayOf1 :: forall m a. MonadRec m => GenT m a -> GenT m (NonEmptyArray a)
arrayOf1 g = sized $ \n -> do
  k <- chooseInt zero n
  x <- g
  xs <- vectorOf (k - one) g
  pure $ unsafePartial fromJust $ NEA.fromArray $ x : xs

-- | Create a random generator which generates a non-empty array of random values.
-- | This is only stack-safe if the underlying monad is stack-safe.
arrayOf1' :: forall m a. Monad m => GenT m a -> GenT m (NonEmptyArray a)
arrayOf1' g = sized $ \n -> do
  k <- chooseInt zero n
  x <- g
  xs <- vectorOf' (k - one) g
  pure $ unsafePartial fromJust $ NEA.fromArray $ x : xs

-- | Create a random generator for a finite enumeration.
-- | `toEnum i` must be well-behaved:
-- | It must return a value wrapped in Just for all Ints between
-- | `fromEnum bottom` and `fromEnum top`.
enum :: forall m a. Monad m => BoundedEnum a => GenT m a
enum = do
  i <- chooseInt (fromEnum (bottom :: a)) (fromEnum (top :: a))
  pure (unsafePartial $ fromJust $ toEnum i)

-- | Stack-safety is guaranteed via the `MonadRec` constraint
replicateMRec :: forall m a. MonadRec m => Int -> m a -> m (List a)
replicateMRec k _ | k <= 0 = pure Nil
replicateMRec k gen = tailRecM go (Tuple Nil k)
  where
  go :: (Tuple (List a) Int) -> m (Step (Tuple (List a) Int) (List a))
  go (Tuple acc 0) = pure $ Done acc
  go (Tuple acc n) = gen <#> \x -> Loop (Tuple (Cons x acc) (n - 1))

-- | Create a random generator which generates a list of random values of the specified size.
-- | Stack-safety is guaranteed via the `MonadRec` constraint
listOf :: forall m a. MonadRec m => Int -> GenT m a -> GenT m (List a)
listOf = replicateMRec

-- | Create a random generator which generates a list of random values of the specified size.
-- | This is only stack-safe if the underlying monad is stack-safe.
listOf' :: forall m a. Monad m => Int -> GenT m a -> GenT m (List a)
listOf' total gen
  | total <= 0 = pure Nil
  | otherwise = replicateM Nil total
      where
      replicateM acc 0 = pure acc
      replicateM acc k = do
        a <- gen
        replicateM (Cons a acc) (k - 1)

-- | Create a random generator which generates a vector of random values of a specified size.
-- | Stack-safety is guaranteed via the `MonadRec` constraint
vectorOf :: forall m a. MonadRec m => Int -> GenT m a -> GenT m (Array a)
vectorOf k g = toUnfoldable <$> listOf k g

-- | Create a random generator which generates a vector of random values of a specified size.
-- | This is only stack-safe if the underlying monad is stack-safe.
vectorOf' :: forall m a. Monad m => Int -> GenT m a -> GenT m (Array a)
vectorOf' k g = toUnfoldable <$> listOf' k g

-- | Create a random generator which selects a value from a non-empty array with
-- | uniform probability.
elements :: forall m a. Monad m => NonEmptyArray a -> GenT m a
elements xs = do
  n <- chooseInt zero (NEA.length xs - one)
  pure $ unsafePartial $ NEA.unsafeIndex xs n

-- | Generate a random permutation of the given array
-- | Stack-safety is guaranteed via the `MonadRec` constraint
shuffle :: forall m a. MonadRec m => Array a -> GenT m (Array a)
shuffle xs = do
  ns <- vectorOf (length xs) (chooseInt 0 top)
  pure (map snd (sortBy (comparing fst) (zip ns xs)))

-- | Generate a random permutation of the given array
-- | This is only stack-safe if the underlying monad is stack-safe.
shuffle' :: forall m a. Monad m => Array a -> GenT m (Array a)
shuffle' xs = do
  ns <- vectorOf' (length xs) (chooseInt 0 top)
  pure (map snd (sortBy (comparing fst) (zip ns xs)))

-- | Sample a random generator
-- | Stack-safety is guaranteed via the `MonadRec` constraint
sample :: forall m a. MonadRec m => Seed -> Int -> GenT m a -> m (Array a)
sample seed sz g = evalGenT (vectorOf sz g) { newSeed: seed, size: sz }

-- | Sample a random generator
-- | This is only stack-safe if the underlying monad is stack-safe.
sample' :: forall m a. Monad m => Seed -> Int -> GenT m a -> m (Array a)
sample' seed sz g = evalGenT (vectorOf' sz g) { newSeed: seed, size: sz }

-- | Generate a single value using a randomly generated seed.
randomSample1 :: forall m a. MonadEffect m => GenT m a -> m a
randomSample1 gen = do
  seed <- liftEffect randomSeed
  evalGenT gen { newSeed: seed, size: 10 }

-- | Sample a random generator, using a randomly generated seed
-- | Stack-safety is guaranteed via the `MonadRec` constraint
randomSampleN :: forall m a. MonadRec m => MonadEffect m => Int -> GenT m a -> m (Array a)
randomSampleN n g = do
  seed <- liftEffect randomSeed
  sample seed n g

-- | Sample a random generator, using a randomly generated seed
-- | This is only stack-safe if the underlying monad is stack-safe.
randomSampleN' :: forall m a. MonadEffect m => Int -> GenT m a -> m (Array a)
randomSampleN' n g = do
  seed <- liftEffect randomSeed
  sample' seed n g

-- | A random generator which simply outputs the current seed
lcgStep :: forall m. Monad m => GenT m Int
lcgStep = GenT $ state f
  where
  f s = Tuple (unSeed s.newSeed) (s { newSeed = lcgNext s.newSeed })

-- | A random generator which approximates a uniform random variable on `[0, 1]`
uniform :: forall m. Monad m => GenT m Number
uniform = (\n -> toNumber n / toNumber lcgM) <$> lcgStep

foreign import float32ToInt32 :: Number -> Int
