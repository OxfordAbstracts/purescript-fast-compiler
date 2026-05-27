//! Single-module e2e tests that should typecheck cleanly.
//!
//! Each test names the feature(s) the fixture exercises. The
//! fixture is a real PureScript source in `fixtures/`. The
//! expectation is always the same: zero errors end-to-end.
//! Failure paths live in [`crate::typecheck_db::tests::failures`].

use super::harness::assert_typechecks;

#[test]
fn record_pun_references_sigless_toplevel_value() {
    // Regression: a record pun must contribute a dependency edge to
    // the punned name so a sig-less top-level value it references is
    // ordered before its user (otherwise UnboundVar).
    assert_typechecks(include_str!("fixtures/single_succeeds/record_pun_sigless_toplevel.purs"));
}

#[test]
fn literals_and_lambda() {
    // Int / Number / String / Char / Boolean literals + `identity`
    // + two-arg `const`.
    assert_typechecks(include_str!("fixtures/single_succeeds/literals_and_lambda.purs"));
}

#[test]
fn let_and_if() {
    // Nested `let` bindings + if-then-else branch unification.
    assert_typechecks(include_str!("fixtures/single_succeeds/let_and_if.purs"));
}

#[test]
fn data_and_case() {
    // ADT declaration + exhaustive case + multi-equation merge
    // + single-field nested constructor recursion.
    assert_typechecks(include_str!("fixtures/single_succeeds/data_and_case.purs"));
}

#[test]
fn newtype_round_trip() {
    // Newtype constructor at value and pattern sites.
    assert_typechecks(include_str!("fixtures/single_succeeds/newtype.purs"));
}

#[test]
fn records() {
    // Closed record literal, open-row field access, record
    // update, pun syntax.
    assert_typechecks(include_str!("fixtures/single_succeeds/records.purs"));
}

#[test]
fn arrays() {
    // Array literal, empty-array polymorphism, array pattern.
    assert_typechecks(include_str!("fixtures/single_succeeds/arrays.purs"));
}

#[test]
fn alias_to_record() {
    // Type alias expanding to a record literal — used in sigs and
    // returned as record literals at call sites (mimics
    // `Data.Traversable.Accum`).
    assert_typechecks(include_str!("fixtures/single_succeeds/alias_to_record.purs"));
}

#[test]
fn class_and_instance() {
    // Single-class definition, one-constructor ADT, instance
    // discharged by the Phase B solver on call-site `show Happy`.
    assert_typechecks(include_str!("fixtures/single_succeeds/class_and_instance.purs"));
}

#[test]
fn instance_context_recursive_solving() {
    // `instance Eq a => Eq (Maybe a)` + `instance Eq Int` —
    // the Phase C fixed-point loop must discharge the outer
    // `Eq (Maybe Int)` and the inner `Eq Int` together.
    assert_typechecks(include_str!("fixtures/single_succeeds/instance_context.purs"));
}

#[test]
fn where_clause_bindings() {
    // `where` clauses are lowered into a synthetic `let` around
    // the body so the clause's names are visible during
    // inference.
    assert_typechecks(include_str!("fixtures/single_succeeds/where_clause.purs"));
}

#[test]
fn compose_polymorphic_record() {
    // Reproducer for the `<<<` direction confusion in
    // `Next.Router.routeChangeError`. When the LHS has a
    // polymorphic record-tail signature, the existing typechecker
    // tried to unify g's input with g's output. See commit msg.
    assert_typechecks(include_str!("fixtures/single_succeeds/compose_polymorphic_record.purs"));
}

#[test]
fn comparing_style_higher_order_class_method() {
    // Mirrors `Data.Ord.comparing` — a polymorphic helper that
    // applies a user-supplied function `f :: a -> b` to two
    // arguments and feeds the results into a class method on
    // `b`. Triggers the kind of inference path that previously
    // produced `Unify(Infinite { var: 1, ty: Fun(Unif(1),
    // Unif(1)) })` when class-method dispatch interacted with
    // SCC pre-registration.
    assert_typechecks(
        "\
module M where

class Ord a where
  compare :: a -> a -> Int

comparing :: forall a b. Ord b => (a -> b) -> a -> a -> Int
comparing f x y = compare (f x) (f y)
",
    );
}

#[test]
fn data_ord_style_module() {
    // Whittled-down reproduction of `Data.Ord`'s shape: a class
    // with a single method, an `Ordering` data type, a fixity
    // declaration aliasing the method to an operator, and a
    // top-level value that uses both the operator and the class
    // method directly. Stresses the same SCC of mutually-related
    // bindings that `Data.Ord` itself does.
    assert_typechecks(
        "\
module M where

data Ordering = LT | EQ | GT

class Ord a where
  compare :: a -> a -> Ordering

lessThan :: forall a. Ord a => a -> a -> Boolean
lessThan a1 a2 = case compare a1 a2 of
  LT -> true
  _ -> false

infixl 4 lessThan as <

comparing :: forall a b. Ord b => (a -> b) -> a -> a -> Ordering
comparing f x y = compare (f x) (f y)
",
    );
}

#[test]
fn class_method_via_backtick_application() {
    // Variant of `data_ord_style_module` that uses backtick syntax
    // (`a `compare` b`) to invoke the class method, mirroring
    // Data.Ord.lessThan's actual style. Backticks are lowered to
    // App nodes; this checks that path stays infinite-type-free.
    assert_typechecks(
        "\
module M where

data Ordering = LT | EQ | GT

class Ord a where
  compare :: a -> a -> Ordering

lessThan :: forall a. Ord a => a -> a -> Boolean
lessThan a1 a2 = case a1 `compare` a2 of
  LT -> true
  _ -> false
",
    );
}

#[test]
fn data_ord_with_full_instance_set() {
    // Closer mirror of Data.Ord: includes the multi-equation
    // `instance ordOrdering` plus a polymorphic value that uses
    // the operator alias. Stresses interaction between
    // multi-equation merge, fixity-target import, and class
    // dispatch — the combination that lights up
    // `Unify(Infinite { var: 1, ty: Fun(Unif(1), Unif(1)) })`
    // when checking the real Prelude module.
    assert_typechecks(
        "\
module M where

data Ordering = LT | EQ | GT

class Ord a where
  compare :: a -> a -> Ordering

instance ordOrdering :: Ord Ordering where
  compare LT LT = EQ
  compare EQ EQ = EQ
  compare GT GT = EQ
  compare LT _ = LT
  compare EQ LT = GT
  compare EQ GT = LT
  compare GT _ = GT

lessThan :: forall a. Ord a => a -> a -> Boolean
lessThan a1 a2 = case a1 `compare` a2 of
  LT -> true
  _ -> false

greaterThan :: forall a. Ord a => a -> a -> Boolean
greaterThan a1 a2 = case a1 `compare` a2 of
  GT -> true
  _ -> false

infixl 4 lessThan as <
infixl 4 greaterThan as >
",
    );
}

#[test]
fn boolean_guard_with_constraint_call() {
    // Smaller still: a value with a boolean guard whose pattern
    // calls a class-constrained function. Reproduces the Data.Ord
    // `between low hi x | x < low = false ...` shape without the
    // surrounding instance/data noise.
    assert_typechecks(
        "\
module M where

class Ord a where
  lt :: a -> a -> Boolean

f :: forall a. Ord a => a -> a -> Boolean
f x y
  | lt x y = false
  | true = true
",
    );
}

#[test]
fn boolean_guard_with_operator_call() {
    // Same as above but the predicate uses an aliased operator
    // (`x < y`) instead of calling the function directly. This
    // should rebracket to `lt x y` during desugar; if it doesn't
    // we'd hit a type mismatch in the guard.
    assert_typechecks(
        "\
module M where

class Ord a where
  lt :: a -> a -> Boolean

infixl 4 lt as <

f :: forall a. Ord a => a -> a -> Boolean
f x y
  | x < y = false
  | true = true
",
    );
}

#[test]
fn between_three_arg_with_two_operators() {
    // Closer to `Data.Ord.between`: a 3-arg function whose body
    // uses two operator aliases in two boolean guards plus a
    // catch-all `true` clause.
    assert_typechecks(
        "\
module M where

class Ord a where
  lt :: a -> a -> Boolean
  gt :: a -> a -> Boolean

infixl 4 lt as <
infixl 4 gt as >

between :: forall a. Ord a => a -> a -> a -> Boolean
between low hi x
  | x < low = false
  | x > hi = false
  | true = true
",
    );
}

#[test]
fn ord_methods_as_top_level_values() {
    // Regression sentinel for the cross-SCC scheme-binding bug
    // that caused `Prelude::Data.Ord` to fail with
    // `Unify(Mismatch(Bool, Fun(_, Bool)))`. Two SCCs (`lt`, `f`)
    // each get a fresh `UnifyState` starting at `Unif(0)`; if `f`
    // sees a stale local-slot for `lt` instead of its scheme, it
    // unifies the wrong arity.
    assert_typechecks(
        "\
module M where

lt a b = true

f x y z
  | lt x y = false
  | true = true
",
    );
}


#[test]
fn generic_sub_style_with_fundep_class() {
    // Mirror `Data.Ring.Generic.genericSub`: a polymorphic value
    // `x y = to $ from x `genericSub'` from y` over a class
    // `Generic a rep | a -> rep` with a fundep. Both `from`/`to`
    // are class methods of the fundep'd class; `genericSub'` is a
    // local class method. Reproduces the
    // `NoInstanceFound on Generic [Fun(..)]` path surfaced by the
    // full Prelude run.
    assert_typechecks(
        "\
module M where

class Generic a rep | a -> rep where
  from :: a -> rep
  to :: rep -> a

class GenericRing r where
  genericSub' :: r -> r -> r

apply :: forall a b. (a -> b) -> a -> b
apply f x = f x

infixr 0 apply as $

genericSub :: forall a rep. Generic a rep => GenericRing rep => a -> a -> a
genericSub x y = to $ from x `genericSub'` from y
",
    );
}

#[test]
fn apply_second_const_identity_chain() {
    // Mirror `Control.Apply.applySecond`: the body
    // `const identity <$> a <*> b` forces the unifier to match
    // `f (a -> b)` from `apply`'s scheme against the
    // already-inferred `f (y -> y)` from `map (const identity)`.
    // Before normalizing `App(App(Con("->"), x), y)` → `Fun(x, y)`
    // at substitution time, that unification failed because the
    // instance-substituted `f` expanded into a constructor-form
    // function type while the body used `Type::Fun`.
    assert_typechecks(
        "\
module M where

class Functor f where
  map :: forall a b. (a -> b) -> f a -> f b

class Functor f <= Apply f where
  apply :: forall a b. f (a -> b) -> f a -> f b

const :: forall a b. a -> b -> a
const x _ = x

identity :: forall a. a -> a
identity x = x

infixl 4 map as <$>
infixl 4 apply as <*>

applySecond :: forall a b f. Apply f => f a -> f b -> f b
applySecond a b = const identity <$> a <*> b
",
    );
}

#[test]
fn control_apply_apply_first_style() {
    // Mirror `Control.Apply.applyFirst`: a polymorphic value
    // whose body is two operator applications. Triggers the
    // `Apply ((->) r)`-related path that surfaced as
    // `Mismatch(Fun(...), App(App(...)))` when checking Prelude.
    assert_typechecks(
        "\
module M where

class Functor f where
  map :: forall a b. (a -> b) -> f a -> f b

class Functor f <= Apply f where
  apply :: forall a b. f (a -> b) -> f a -> f b

const :: forall a b. a -> b -> a
const x _ = x

infixl 4 map as <$>
infixl 4 apply as <*>

identity :: forall a. a -> a
identity x = x

applyFirst :: forall a b f. Apply f => f a -> f b -> f a
applyFirst a b = const <$> a <*> b

applySecond :: forall a b f. Apply f => f a -> f b -> f b
applySecond a b = const identity <$> a <*> b

lift2 :: forall a b c f. Apply f => (a -> b -> c) -> f a -> f b -> f c
lift2 f a b = f <$> a <*> b

lift3 :: forall a b c d f. Apply f => (a -> b -> c -> d) -> f a -> f b -> f c -> f d
lift3 f a b c = f <$> a <*> b <*> c
",
    );
}

#[test]
fn backtick_default_precedence_nine_binds_tighter_than_named_op() {
    // Sentinel: `p `mod` 2 == 0` must rebracket as `(p `mod` 2)
    // == 0`, not as `p `mod` (eq 2 0)`. Backtick application
    // defaults to `infixl 9` (PureScript reference) so it binds
    // tighter than `==` (infixl 4). With the wrong default
    // (`infixl 1`) the inner `eq 2 0` becomes the second
    // operand to `mod` and forces `EuclideanRing Boolean`.
    assert_typechecks(
        "\
module M where

class Eq a where
  eq :: a -> a -> Boolean

class EuclideanRing a where
  div :: a -> a -> a
  mod :: a -> a -> a

instance eqInt :: Eq Int where
  eq _ _ = true

instance euclideanRingInt :: EuclideanRing Int where
  div _ _ = 0
  mod _ _ = 0

infixl 4 eq as ==

go :: Int -> Boolean
go p
  | p `mod` 2 == 0 = true
  | true = false
",
    );
}

#[test]
fn do_notation_binds_maybe_via_local_instance() {
    // Mirror `passing/Do.purs`: a local `Bind Maybe` instance and
    // a `do`-block that should desugar to `bind` calls. The
    // `Bind Maybe` constraint arising from the first `Just 1.0`
    // must be discharged against the local instance.
    assert_typechecks(
        "\
module M where

data Maybe a = Nothing | Just a

class Functor f where
  map :: forall a b. (a -> b) -> f a -> f b

class Functor f <= Apply f where
  apply :: forall a b. f (a -> b) -> f a -> f b

class Apply f <= Bind f where
  bind :: forall a b. f a -> (a -> f b) -> f b

instance functorMaybe :: Functor Maybe where
  map fn (Just x) = Just (fn x)
  map _  _        = Nothing

instance applyMaybe :: Apply Maybe where
  apply (Just fn) (Just x) = Just (fn x)
  apply _         _        = Nothing

instance bindMaybe :: Bind Maybe where
  bind Nothing  _ = Nothing
  bind (Just a) f = f a

test = \\_ -> do
  x <- Just 1
  y <- Just 2
  Just x
",
    );
}

#[test]
fn multi_equation_first_clause_has_constructor_in_later_column() {
    // Regression: `maybe b _ Nothing = b; maybe _ f (Just a) = f a`
    // from Data.Maybe. The first equation has a `Nothing` pattern
    // in column 2 while its earlier columns are variables. The
    // exhaustiveness check must walk each alt's column 2 binders
    // to see both `Nothing` and `Just a`. A prior bug ignored
    // alts whose earlier columns contained no refutable patterns,
    // leading to a spurious "missing Nothing" diagnostic.
    assert_typechecks(
        "\
module M where

data Maybe a = Nothing | Just a

maybe :: forall a b. b -> (a -> b) -> Maybe a -> b
maybe b _ Nothing = b
maybe _ f (Just a) = f a
",
    );
}

#[test]
fn record_with_polymorphic_fields_instantiates_per_access() {
    // Mirror `passing/Monad.purs`: the record stored in `m` has
    // polymorphic fields (`return :: forall a. a -> m a`); each
    // access `m.return` has to instantiate the quantifier fresh
    // so repeated uses pick independent `a`s.
    assert_typechecks(
        "\
module M where

data Id a = Id a
data Maybe a = Nothing | Just a

type Mon m = { return :: forall a. a -> m a }

test :: forall m. Mon m -> m Number
test m = m.return 1.0

test2 :: forall m. Mon m -> m String
test2 m = m.return \"hi\"
",
    );
}

#[test]
fn tail_rec_exact_reproduction() {
    // Exact copy of Control.Monad.Rec.Class.tailRec.
    assert_typechecks(
        "\
module M where

data Step a b = Loop a | Done b
data Unit = Unit

class Functor f where
  map :: forall a b. (a -> b) -> f a -> f b

voidRight :: forall f a b. Functor f => a -> f b -> f a
voidRight x f = map (\\_ -> x) f

class Functor f <= Apply f where
  apply :: forall a b. f (a -> b) -> f a -> f b

class Apply f <= Bind f where
  bind :: forall a b. f a -> (a -> f b) -> f b

class Apply f <= Applicative f where
  pure :: forall a. a -> f a

class (Applicative m, Bind m) <= Monad m
class Monad m <= MonadRec m where
  tailRecM :: forall a b. (a -> m (Step a b)) -> a -> m b

compose :: forall a b c. (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)

infixr 9 compose as <<<
infixl 4 voidRight as <$

unit :: Unit
unit = Unit

tailRec :: forall a b. (a -> Step a b) -> a -> b
tailRec f = go <<< f
  where
  go (Loop a) = go (f a)
  go (Done b) = b

forever :: forall m a b. MonadRec m => m a -> m b
forever ma = tailRecM (\\u -> Loop u <$ ma) unit
",
    );
}

#[test]
fn where_clause_multi_equation_step_dispatch() {
    // Mirror `Control.Monad.Rec.Class.tailRec`'s where-clause
    // shape: `go` defined by two pattern-matching equations
    // against a `Step` constructor. The let-binding multi-eq
    // merger has to collapse them into one case-dispatched
    // lambda so inference sees both branches.
    assert_typechecks(
        "\
module M where

data Step a b = Loop a | Done b

tailRec :: forall a b. (a -> Step a b) -> a -> b
tailRec f = go
  where
  go x = case f x of
    Loop a -> go a
    Done b -> b
",
    );
}

#[test]
fn where_clause_multi_equation_pattern_matched_lambda() {
    // Same as `where_clause_multi_equation_step_dispatch` but
    // written in the multi-equation style that the let-binding
    // merger has to desugar into a case-dispatched lambda.
    assert_typechecks(
        "\
module M where

data Step a b = Loop a | Done b

compose :: forall a b c. (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)

infixr 9 compose as <<<

tailRec :: forall a b. (a -> Step a b) -> a -> b
tailRec f = go <<< f
  where
  go (Loop a) = go (f a)
  go (Done b) = b
",
    );
}

#[test]
fn instance_method_multi_equation_merges() {
    // Regression: two adjacent `map` equations inside an
    // `instance Functor Maybe` block must merge into a single
    // case expression so exhaustiveness sees both alternatives.
    // Without the recursive `multi_eq::merge` call inside
    // `Decl::Instance.members`, only the first equation reaches
    // inference and the checker reports a spurious
    // "missing Nothing" case.
    assert_typechecks(
        "\
module M where

data Maybe a = Nothing | Just a

class Functor f where
  map :: forall a b. (a -> b) -> f a -> f b

instance functorMaybe :: Functor Maybe where
  map fn (Just x) = Just (fn x)
  map _  _        = Nothing
",
    );
}

#[test]
fn data_monoid_guard_pattern_via_multi_equation() {
    // Mirror `Data.Monoid.guard`: a value with two equations,
    // pattern-matching on a Boolean literal in the first arg.
    // Multi-equation merge turns this into a case expression;
    // the second equation's body uses a class method (`mempty`)
    // whose constraint must defer cleanly.
    assert_typechecks(
        "\
module M where

class Monoid m where
  mempty :: m

guard :: forall m. Monoid m => Boolean -> m -> m
guard true a = a
guard false _ = mempty
",
    );
}

#[test]
fn euclidean_ring_style_with_disj_in_guard() {
    // Closer mirror of `Data.EuclideanRing.lcm`: the `if`'s
    // condition uses `disj` (the `||` operator), which is
    // `HeytingAlgebra a => a -> a -> a`. The two operands have
    // type `Boolean` (from `eq`), so `||` resolves at `Boolean`.
    // The `then` branch is `zero` — its type must NOT collapse
    // to `Boolean` (it's `α`, the lcm's parameter type) even
    // though the condition's type is `Boolean`.
    assert_typechecks(
        "\
module M where
class Eq a where
  eq :: a -> a -> Boolean

class Semiring a where
  zero :: a
  one :: a
  add :: a -> a -> a
  mul :: a -> a -> a

class HeytingAlgebra a where
  disj :: a -> a -> a

instance heytingAlgebraBoolean :: HeytingAlgebra Boolean where
  disj _ _ = true

infixl 4 eq as ==
infixr 2 disj as ||

lcm :: forall a. Eq a => Semiring a => a -> a -> a
lcm a b = if a == zero || b == zero then zero else zero
",
    );
}

#[test]
fn euclidean_ring_style_recursive_with_classes() {
    // Mirror `Data.EuclideanRing.gcd`: a polymorphic value with
    // an explicit `Eq a => EuclideanRing a =>` signature whose
    // body uses class methods (`zero` from `Semiring`, `==`
    // from `Eq`, `mod` from `EuclideanRing`) plus a recursive
    // call to itself. Constraints involving fresh unif vars
    // should defer, not surface as `NoInstanceFound`.
    assert_typechecks(
        "\
module M where

data Ordering = LT | EQ | GT

class Eq a where
  eq :: a -> a -> Boolean

class Semiring a where
  zero :: a
  one :: a
  add :: a -> a -> a
  mul :: a -> a -> a

class Semiring a <= Ring a where
  sub :: a -> a -> a

class Ring a <= CommutativeRing a

class CommutativeRing a <= EuclideanRing a where
  div :: a -> a -> a
  mod :: a -> a -> a

infixl 4 eq as ==

infixl 7 mul as *
infixl 7 div as /

gcd :: forall a. Eq a => EuclideanRing a => a -> a -> a
gcd a b =
  if b == zero then a
  else gcd b (a `mod` b)

lcm :: forall a. Eq a => EuclideanRing a => a -> a -> a
lcm a b =
  if a == zero then zero
  else if b == zero then zero
  else (a * b) / gcd a b
",
    );
}
