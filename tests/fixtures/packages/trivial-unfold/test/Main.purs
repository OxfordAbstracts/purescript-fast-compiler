module Test.Main where

import Prelude

import Effect (Effect)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldSatisfy, AnyShow(..))
import Test.QuickCheck ((===), (<?>), class Testable)
import Test.QuickCheck.Arbitrary (class Arbitrary, class Coarbitrary)
import Test.Spec.QuickCheck (quickCheck, quickCheck')
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Test.Spec.Reporter.June.Pretty (prettyReporter)
import Effect.Aff (Aff)
import Effect.Exception as Effect.Exception
import Pipes ((>->), yield, await)
import Pipes.Core (Producer_, Consumer_)
import Pipes.Core as Pipes -- I am NOT importing something called "runEffect" unqualified lol
import Control.Monad.Trans.Class (lift)
import Control.Monad.Error.Class (class MonadThrow)

import Data.Unfoldable.Trivial.Internal
  ( Trivial
  , trivial
  , runTrivial
  , (::<*>)
  )

import Data.Unfoldable1.Trivial1.Internal
  ( Trivial1
  , runTrivial1
  , (::<+>)
  )

import Data.Unfoldable.Trivial
  ( head1
  , head
  , tail
  , last1
  , last
  , init
  , index
  , foldEnum
  , iterate
  , uncons
  , cons
  , snoc
  , refoldMap
  , refoldMap1
  , take
  , take1
  , index1
  , append1
  , append1'
  , drop
  )

import Data.Unfoldable.MaybeEmpty
  ( MaybeEmpty(..)
  , distributeMaybesA
  , toAlternative
  )

import Data.Maybe (Maybe(..), isJust, isNothing)
import Control.Alternative ((<|>), guard, empty, class Alternative, class Plus, class Alt)
import Data.Enum (class Enum, class BoundedEnum, succ, pred, upFrom, downFrom, upFromIncluding, enumFromTo)
import Data.Tuple (snd)
import Data.Tuple.Nested ((/\), type (/\))
import Data.Semigroup.First (First(..))
import Data.Semigroup.Last (Last(..))
import Data.Unfoldable (none, fromMaybe, replicate)
import Data.Unfoldable1 (singleton, replicate1, unfoldr1)
import Data.Foldable (foldl, foldr, foldMap, foldMapDefaultL, foldMapDefaultR, intercalate, length)
import Data.Semigroup.Foldable (foldl1, foldr1, foldMap1DefaultL, foldMap1DefaultR)
import Type.Proxy (Proxy(..))
import Data.Array (toUnfoldable, zipWith)
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Monoid.Multiplicative (Multiplicative(..))
import Data.Newtype (un, ala)
import Data.Compactable (compact, applyMaybe)
import Control.Extend (duplicate)
import Data.Identity (Identity)
import Data.Distributive (distribute)
import Data.List.NonEmpty as NEL

iff :: forall a. Boolean -> a -> Maybe a
iff = ($>) <<< guard

oughta :: forall f m t. Functor f => Show (f (AnyShow t)) => MonadThrow Effect.Exception.Error m => f t -> (f (AnyShow t) -> Boolean) -> m Unit
oughta = map AnyShow >>> shouldSatisfy

arrgh :: forall a. Trivial a -> Array a
arrgh = runTrivial

arrgh1 :: forall a. Trivial1 a -> Array a
arrgh1 = runTrivial1

main :: Effect Unit
main = runSpecAndExitProcess [prettyReporter] do
  smallSuite
  compareSuite
  buildSuite
  foldSuite
  appendSuite
  applySuite
  enumSuite
  newtypesSuite
  filterSuite
  exampleInTheReadmeTest

smallSuite :: Spec Unit
smallSuite = describe "small stuff" do
  it "single uncons" do
    map (map trivial) (uncons none) `oughta` isNothing
    map (map trivial) (uncons $ singleton unit) `oughta` isJust
  it "head is sane" do
    quickCheck \(x :: Int) -> head (singleton x) === Just x
    quickCheck \(x :: Int) -> head1 (singleton x) === x
    quickCheck \(x :: Maybe String) -> head (fromMaybe x) === x
    quickCheck \x -> head (replicate x "ehehe") === iff (x > 0) "ehehe"
    quickCheck \x (y :: Int) -> head (replicate1 x y) === Just y
  it "last is sane" do
    quickCheck' 5 \(x :: Int) -> last (singleton x) === Just x
    quickCheck' 5 \(x :: Int) -> last1 (singleton x) === x
    quickCheck' 5 \(x :: Maybe String) -> last (fromMaybe x) === x
    quickCheck' 5 \x -> last (replicate x "ehehe") === iff (x > 0) "ehehe"
    quickCheck' 5 \x (y :: Int) -> last (replicate1 x y) === Just y
  it "double uncons" do
    let double :: forall a. Trivial a -> Maybe (a /\ Maybe a)
        double = map (map head) <<< uncons
    quickCheck \(x :: Int) -> double (singleton x) === Just (x /\ Nothing)
    quickCheck \x -> isJust (snd =<< double (replicate1 x unit)) === (x > 1)
  it "head tail gets second element" do
    head (tail none) `oughta` isNothing
    quickCheck \(x :: String) -> head (tail $ singleton x) === Nothing
    quickCheck \(x :: Char) -> head (tail $ upFrom x) === (succ =<< succ x)
    quickCheck \(x :: Trivial Int) -> head (tail x) === index x 1
  it "last tail gets last" do
    quickCheck' 15 \(x :: String) -> last (tail $ singleton x) === Nothing
    quickCheck' 15 \(x :: Trivial Int) -> last (tail x) === tail x *> last x
  it "last init gets second to last" do
    quickCheck' 25 \(x :: String) -> last (init $ singleton x) === Nothing
    quickCheck' 15 \(x :: Char) y -> last (init $ enumFromTo x y) === case compare x y of
      LT -> pred y
      GT -> succ y
      EQ -> Nothing
  it "Maybe round trip" do
    quickCheck \(x :: Maybe Char) -> runTrivial (fromMaybe x) === x
  it "take <> drop" do
    quickCheck \(x :: Trivial Int) n -> refoldMap singleton (take n x) <> refoldMap singleton (drop n x) === (runTrivial x :: Array _)
  it "take agrees with index" do
    quickCheck \(x :: Trivial Char) n -> refoldMap (Just <<< Last) (take n x) === Last <$> index x ((min n $ length x) - 1)
  it "drop agrees with index" do
    quickCheck \(x :: Trivial Char) n -> drop n x === index x (max n 0)
  it "take1 agrees with index1" do
    quickCheck \(x :: Trivial1 Char) n -> refoldMap1 Last (take1 n x) === (Last $ index1 x (clamp 0 (length x - 1) (n - 1)))
  
compareSuite :: Spec Unit
compareSuite = describe "Eq and Ord" do
  let qc = quickCheck' 20 :: forall p. Testable p => p -> _
  it "Eq1 Trivial1 is reflexive" do
    qc \(x :: Trivial1 Int) -> x === x
  it "Eq1 Trivial is reflexive" do
    qc \(x :: Trivial Int) -> x === x
  it "Eq1 Trivial1 agrees with Eq1 Array" do
    qc \(x :: Trivial1 Boolean) y -> (x == y) === (arrgh1 x == arrgh1 y)
  it "Eq1 Trivial agrees with Eq1 Array" do
    qc \(x :: Trivial Boolean) y -> (x == y) === (arrgh x == arrgh y)
  it "Ord1 Trivial1 compares equal values as EQ" do
    qc \(x :: Trivial1 Number) -> compare x x === EQ
  it "Ord1 Trivial compares equal values as EQ" do
    qc \(x :: Trivial Number) -> compare x x === EQ
  it "Ord1 Trivial1 agrees with Ord1 Array" do
    qc \(x :: Trivial1 Number) y -> compare x y == compare (arrgh1 x) (arrgh1 y) <?> show (arrgh1 x) <> "\n\tcompared wrong with\n" <> show (arrgh1 y)
  it "Ord1 Trivial agrees with Ord1 Array" do
    qc \(x :: Trivial Number) y -> compare x y == compare (arrgh x) (arrgh y) <?> show (arrgh x) <> "\n\tcompared wrong with\n" <> show (arrgh y)

buildSuite :: Spec Unit
buildSuite = describe "build" do
  it "build on none" do
    quickCheck \(x :: Int) -> cons x none === Just x
    quickCheck \(x :: Int) -> snoc none x === Just x
  it "build on singleton" do
    quickCheck \x (y :: Int) -> cons x (singleton y) === Just x
    quickCheck \x (y :: Int) -> tail (cons x $ singleton y) === Just y
    quickCheck \x (y :: Int) -> snoc (singleton y) x === Just y
    quickCheck \x (y :: Int) -> tail (snoc (singleton y) x) === Just x
  it "build on Unfoldable1" do
    quickCheck \x (y :: Trivial1 Int) -> cons x (runTrivial1 y) === Just x
    quickCheck \x (y :: Trivial1 Int) -> head1 (snoc (runTrivial1 y) x) === head1 y
    quickCheck \x (y :: Trivial1 Int) -> tail (cons x $ runTrivial1 y) === Just (head1 y)
    quickCheck \x (y :: Trivial1 Int) -> tail (snoc (runTrivial1 y) x) === index (runTrivial1 y) 1 <|> Just x

foldSuite :: Spec Unit
foldSuite = describe "foldl foldr" do
  describe "Foldable Trivial1" do
    it "associative string concatenation agrees" do
      quickCheck' 15 \(u :: Trivial1 String) ->
        foldMapDefaultL identity u === foldMapDefaultR identity u
  describe "Foldable Trivial" do
    it "associative string concatenation agrees" do
      quickCheck' 15 \(u :: Trivial String) ->
        foldMapDefaultL identity u === foldMapDefaultR identity u
    it "empty folds" do 
      quickCheck \(f :: Int -> String -> Int) x -> (foldl f x ::<*> none) === x
      quickCheck \(f :: String -> Int -> Int) x -> (foldr f x ::<*> none) === x
  describe "Foldable1 Trivial1" do
    it "associative string concatenation agrees" do
      quickCheck' 15 \(u :: Trivial1 String) ->
        foldMap1DefaultL identity u === foldMap1DefaultR identity u
    it "singleton folds" do 
      quickCheck \f (x :: Int) -> (foldl1 f ::<+> singleton x) === x
      quickCheck \f (x :: Int) -> (foldr1 f ::<+> singleton x) === x

appendSuite :: Spec Unit
appendSuite = describe "Semigroup and Alternative" do
  let qc = quickCheck' 15 :: forall p. Testable p => p -> _
  it "Semigroup (Trivial a) agrees with Alt Array" do
    qc \(a :: Trivial Char) b -> arrgh (a <> b) === arrgh a <|> arrgh b
  it "Semigroup (Trivial1 a) agrees with Alt Array" do
    qc \(a :: Trivial1 Char) b -> arrgh1 (a <> b) === arrgh1 a <|> arrgh1 b
  it "append1 agrees with Alt Array" do
    qc \(a :: Trivial1 Char) (b :: Trivial Char) -> arrgh1 (a `append1` b) === arrgh1 a <|> arrgh b
  it "append1' agrees with Alt Array" do
    qc \(a :: Trivial Char) (b :: Trivial1 Char) -> arrgh1 (a `append1'` b) === arrgh a <|> arrgh1 b
  it "Alt Trivial1 agrees with Alt Trivial" do
    qc \x y -> runTrivial1 (x <|> y) === runTrivial1 x <|> (runTrivial1 y :: Trivial Number)
  genericAlternativeLaws "Trivial" qc (Proxy :: Proxy (Trivial Int))
  genericAltLaws "Trivial1" qc (Proxy :: Proxy (Trivial1 Int))
  genericAlternativeLaws "MaybeEmpty Identity" qc (Proxy :: Proxy (MaybeEmpty Identity Int))
  genericAlternativeLaws "MaybeEmpty Maybe" qc (Proxy :: Proxy (MaybeEmpty Maybe Int))
  genericAlternativeLaws "MaybeEmpty NonEmptyArray" qc (Proxy :: Proxy (MaybeEmpty NonEmptyArray Int))

genericAltLaws :: forall t a.
  Eq (t a) =>
  Show (t a) =>
  Alt t =>
  Arbitrary a =>
  Coarbitrary a => 
  Arbitrary (t a) =>
  String -> (forall p. Testable p => p -> Aff Unit) -> Proxy (t a) -> Spec Unit
genericAltLaws name qc _ = describe ("Alt " <> name <> " laws") do
  it "Associativity: (x <|> y) <|> z ≡ x <|> (y <|> z)" do
    qc \(x :: t a) y z -> (x <|> y) <|> z === x <|> (y <|> z)
  it "Distributivity: f <$> (x <|> y) ≡ (f <$> x) <|> (f <$> y)" do
    qc \(f :: a -> a) (x :: t a) y -> f <$> (x <|> y) === (f <$> x) <|> (f <$> y)

genericPlusLaws :: forall t a.
  Eq (t a) =>
  Show (t a) =>
  Plus t =>
  Arbitrary a =>
  Coarbitrary a => 
  Arbitrary (t a) =>
  Arbitrary (t (a -> a)) =>
  String -> (forall p. Testable p => p -> Aff Unit) -> Proxy (t a) -> Spec Unit
genericPlusLaws name qc proxy = do
  genericAltLaws name qc proxy
  describe ("Plus " <> name <> " laws") do
    it "Left identity: empty <|> x ≡ x" do
      qc \(x :: t a) -> empty <|> x === x
    it "Right identity: x <|> empty ≡ x" do
      qc \(x :: t a) -> x <|> empty === x
    it "Annihilation: f <$> empty ≡ empty" do
      qc \(f :: a -> a) -> f <$> empty === (empty :: t a)

genericAlternativeLaws :: forall t a.
  Eq (t a) =>
  Show (t a) =>
  Alternative t =>
  Arbitrary a =>
  Coarbitrary a => 
  Arbitrary (t a) =>
  Arbitrary (t (a -> a)) =>
  String -> (forall p. Testable p => p -> Aff Unit) -> Proxy (t a) -> Spec Unit
genericAlternativeLaws name qc proxy = do
  genericAltLaws name qc proxy
  genericPlusLaws name qc proxy
  describe ("Alternative " <> name <> " laws") do
    it "Distributivity: (f <|> g) <*> x ≡ (f <*> x) <|> (g <*> x)" do
      qc \(f :: t (a -> a)) g x -> (f <|> g) <*> x === (f <*> x) <|> (g <*> x)
    it "Annihilation: empty <*> f ≡ empty" do
      qc \(f :: t a) -> empty <*> f === (empty :: t a)

applySuite :: Spec Unit
applySuite = describe "Apply and Applicative" do
  let qc = quickCheck' 10 :: forall p. Testable p => p -> _
  it "Apply Trivial agrees with zipWith on arrays" do
    qc \(f :: String -> Char -> Int) a b -> arrgh (f <$> a <*> b) === zipWith f (arrgh a) (arrgh b)
  it "Apply Trivial1 agrees with zipWith on arrays" do
    qc \(f :: String -> Char -> Int) a b -> arrgh1 (f <$> a <*> b) === zipWith f (arrgh1 a) (arrgh1 b)
  genericApplicativeLaws "Trivial" qc (take 25 :: _ -> _ Int)
  genericApplicativeLaws "Trivial1" qc (take1 25 :: _ -> _ Int)
  genericApplicativeLaws "MaybeEmpty Identity" qc (identity :: _ -> MaybeEmpty Identity Int)
  genericApplicativeLaws "MaybeEmpty Maybe" qc (identity :: _ -> MaybeEmpty Maybe Int)
  genericApplicativeLaws "MaybeEmpty NonEmptyArray" qc (identity :: _ -> MaybeEmpty NonEmptyArray Int)

genericApplicativeLaws :: forall t a.
  Eq (t a) =>
  Show (t a) =>
  Applicative t =>
  Arbitrary a =>
  Coarbitrary a => 
  Arbitrary (t a) =>
  Arbitrary (t (a -> a)) =>
  String -> (forall p. Testable p => p -> Aff Unit) -> (t a -> t a) -> Spec Unit
genericApplicativeLaws name qc witness = describe ("Applicative " <> name <> " identities") do
  it "Associative composition: (<<<) <$> f <*> g <*> h ≡ f <*> (g <*> h)" do
    qc \(f :: t (a -> a)) g (h :: t a) -> (<<<) <$> f <*> g <*> h === f <*> (g <*> h)
  it "Identity: (pure identity) <*> v ≡ v" do
    qc \(v :: t a) -> (pure identity) <*> v === v
  it "Composition: pure (<<<) <*> f <*> g <*> h ≡ f <*> (g <*> h)" do
    qc \(f :: t (a -> a)) g (h :: t a) -> pure (<<<) <*> f <*> g <*> h === f <*> (g <*> h)
  it ("Homomorphism: (pure f) <*> (pure x) ≡ pure (f x) -- checked up to a limit if pure :: " <> name <> " a is infinite") do
    qc \(f :: a -> a) x -> witness ((pure f) <*> (pure x)) === witness (pure (f x))
  it "Interchange: u <*> (pure y) ≡ (pure (_ $ y)) <*> u" do
    qc \(u :: t (a -> a)) y -> u <*> (pure y) === (pure (_ $ y)) <*> u

enumSuite :: Spec Unit
enumSuite = describe "enums" do
  genericEnumSuite "Int" (Proxy :: Proxy Int) do
    it "index matches upFromIncluding" do
      quickCheck' 5 \x y -> index (upFromIncluding x) y === iff (y >= 0) (x + y)
    it "index matches iterate" do
      quickCheck' 5 \x -> index (iterate (_+1) 0) x === iff (x >= 0) x
  genericBoundedEnumSuite "Char" (Proxy :: Proxy Char) $ pure unit
  genericBoundedEnumSuite "Ordering" (Proxy :: Proxy Ordering) $ pure unit
  genericBoundedEnumSuite "Boolean" (Proxy :: Proxy Boolean) $ pure unit
  genericBoundedEnumSuite "Unit" (Proxy :: Proxy Unit) $ pure unit -- ...what was I thinking of doing for bounded extras again

genericEnumSuite :: forall a. Enum a => Arbitrary a => Show a =>
  String -> Proxy a -> Spec Unit
 -> Spec Unit

genericEnumSuite name _ extras = describe name do
  it "directionality" do
    quickCheck' 100 \(x :: a) -> head (upFrom x) === succ x
    quickCheck' 100 \(x :: a) -> head (downFrom x) === pred x
  extras

genericBoundedEnumSuite :: forall a. BoundedEnum a => Arbitrary a => Show a =>
  String -> Proxy a -> Spec Unit
 -> Spec Unit

genericBoundedEnumSuite name p extras = genericEnumSuite name p $ (_ *> extras) do
  it "ends are in right order" do
    First bottom `shouldEqual` foldEnum (First :: a -> First a)
    Last top `shouldEqual` foldEnum (Last :: a -> Last a)

newtypesSuite :: Spec Unit
newtypesSuite = describe "Newtypes" do
  it "empty MaybeEmpty is Nothing" do
    (Nothing :: Maybe (NEL.NonEmptyList Unit)) `shouldEqual` un MaybeEmpty none
  it "MaybeEmpty Maybe Int agrees with Extend Maybe" do
    quickCheck \(x :: Trivial Int) -> un MaybeEmpty (runTrivial x) === duplicate (runTrivial x)
  it "NonEmptyList always roundtrips intact" do
    quickCheck \(x :: NEL.NonEmptyList String) -> un MaybeEmpty (NEL.toUnfoldable x) === Just x
  it ("distributeMaybes would agree with Distributive Identity... " <>
        "if Identity had an Unfoldable1 instance, which it just doesn't for some reason") do
    quickCheck \(x :: Maybe (Identity Char)) -> distributeMaybesA (MaybeEmpty x) === distribute x
  it "toAlternative agrees with Monad Array" do
    quickCheck \(x :: Array Number) -> join (toAlternative $ toUnfoldable x) === x
  it "Foldable MaybeEmpty Trivial1 agrees with Foldable Trivial" do
    let the :: forall a. Trivial a -> MaybeEmpty Trivial1 a
        the = runTrivial
    quickCheck' 40 \(x :: Trivial Char) (f :: Char -> Int -> Int) y -> foldr f y (the x) === foldr f y x
    quickCheck' 40 \(x :: Trivial Char) (f :: Int -> Char -> Int) y -> foldl f y (the x) === foldl f y x
    quickCheck' 40 \(x :: Trivial Char) (f :: Char -> String) -> foldMap f (the x) === foldMap f x

filterSuite :: Spec Unit
filterSuite = describe "Compactable and Filterable" do
  it "Functor identity: compact <<< map Just ≡ id" do
    quickCheck \(x :: Trivial String) -> runTrivial (compact ::<*> map Just x) === (runTrivial :: Trivial String -> Array String) x
  it "Applicative identity: compact <<< (pure Just <*> _) ≡ id" do
    quickCheck \(x :: Trivial Int) -> arrgh (compact $ pure Just <*> x) === arrgh x
  it "Applicative identity: applyMaybe (pure Just) ≡ id" do
    quickCheck \(x :: Trivial Int) -> arrgh (applyMaybe (pure Just) x) === arrgh x
  it "Applicative identity: compact ≡ applyMaybe (pure id)" do
    quickCheck \(x :: Trivial (Maybe String)) -> arrgh (compact x) === arrgh (applyMaybe (pure identity) x)
  it "Plus identity: compact empty ≡ empty" do
    runTrivial (compact empty) `shouldEqual` ([] :: Array Int)
  it "Plus identity: compact (const Nothing <$> xs) ≡ empty, except ^" do
    quickCheck \(x :: Trivial Char) -> runTrivial (compact (const (Nothing :: Maybe Char) <$> x)) === []

-- because it would be ESPECIALLY embarrassing if this didn't work :P
exampleInTheReadmeTest :: Spec Unit
exampleInTheReadmeTest = it "Example in the README" $
  Pipes.runEffect $ exampleInTheReadme >-> do
    equals $ Just 'z'
    equals   "gonna give you up"
    equals   720
  where equals :: forall a. Show a => a -> Consumer_ String Aff Unit
        equals value = await >>= lift <<< shouldEqual (show value)

-- it took me embarrassingly long to fully realize Identity doesn't just, like,
-- automatically coerce to literally any other monad :p
exampleInTheReadme :: forall m. Monad m => Producer_ String m Unit
exampleInTheReadme = do
  -- ehehehehe
  let logShow :: forall a. Show a => a -> _
      logShow = yield <<< show
  
  -- Imports to show in actual example
  {-
  import Effect.Console (logShow)
  import Data.Enum (upFrom)
  import Data.Maybe (Maybe(..))
  import Data.Array (toUnfoldable)
  import Data.Foldable (intercalate)
  import Data.Monoid (guard)
  import Data.Unfoldable (unfoldr1)
  import Data.Newtype (ala)
  import Data.Multiplicative (Multiplicative(..))

  import Data.Unfoldable.Trivial (index, drop, refoldMap1, (::<*>))
  -}

  -- main = do

  -- Index into a very large range without evaluating all of it.
  logShow $ index (upFromIncluding 'A') $ 32 + 25
  -- > Just 'z'

  -- Fold over a suffix of an Array without constructing a new Array for
  -- the suffix.
  -- The (::<*>) operator is ($) specialized to Trivial,
  -- and (::<+>) likewise for Trivial1,
  -- to conveniently make instances decidable.
  -- (Note that this can also be accomplished with Data.List.Lazy.)
  logShow $ intercalate " " ::<*> drop 2 $ toUnfoldable [
    "I'm", "never", "gonna", "give", "you", "up"
  ]
  -- > "gonna give you up"

  -- Fold directly from a generating function.
  -- Basic folds are also provided specialized, with the "re-" prefix;
  -- i.e. `refoldMap1 Multiplicative $ unfoldr1 fact 1` is equivalent to
  --      `foldMap1 Multiplicative ::<+> unfoldr1 fact 1`.
  let fact n = n /\ (guard (n < 6) $> n + 1)
  logShow $ ala Multiplicative refoldMap1 $ unfoldr1 fact 1
  -- > 620
