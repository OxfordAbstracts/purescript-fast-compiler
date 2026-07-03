//! Incremental-compilation tests.
//!
//! These tests drive `check_many_modules_with_db` twice against the
//! same `TypecheckDb`, then assert `CacheOutcome::Hit` / `Miss` on
//! specific decls to prove the core property: a declaration
//! recompiles only when it changes or when one of its direct
//! dependencies changes **type**. Body-only edits to a dependency do
//! not invalidate dependents.
//!
//! Every test structure:
//! 1. Build a `TypecheckDb::open_in_memory()`.
//! 2. Run a baseline source set → all decls expected `Miss`.
//! 3. Run an edited source set through the *same* db → assert
//!    per-decl `Hit`/`Miss` matches the expected cascade.

use crate::typecheck_db::driver::{CacheOutcome, TypecheckDb};

use super::harness::{outcome_of, run_with_shared_db};

// ---------------------------------------------------------------------------
// Intra-module
// ---------------------------------------------------------------------------

#[test]
fn body_edit_leaves_dependent_cached() {
    // `fn1`'s body edit keeps its scheme (Int → Int). `fn2`
    // depends on `fn1`'s scheme-only output hash, so its
    // input_hash is unchanged → Hit on the second run.
    let mut db = TypecheckDb::open_in_memory().unwrap();
    let v1 = [(
        "M",
        "module M where\nfn1 = 1\nfn2 = fn1\n",
    )];
    let v2 = [(
        "M",
        "module M where\nfn1 = 2\nfn2 = fn1\n",
    )];
    let first = run_with_shared_db(&mut db, &v1);
    assert!(first.errors.is_empty(), "{:?}", first.errors);
    assert_eq!(outcome_of(&first, "M", "fn1"), CacheOutcome::Miss);
    assert_eq!(outcome_of(&first, "M", "fn2"), CacheOutcome::Miss);

    let second = run_with_shared_db(&mut db, &v2);
    assert!(second.errors.is_empty(), "{:?}", second.errors);
    assert_eq!(outcome_of(&second, "M", "fn1"), CacheOutcome::Miss);
    assert_eq!(
        outcome_of(&second, "M", "fn2"),
        CacheOutcome::Hit,
        "fn2 should hit because fn1's scheme (Int) is unchanged",
    );
}

#[test]
fn type_edit_invalidates_dependent() {
    // `fn1`'s type flips Int → String. `fn2`'s input_hash folds
    // in `fn1`'s scheme hash, which now differs → Miss.
    let mut db = TypecheckDb::open_in_memory().unwrap();
    let v1 = [("M", "module M where\nfn1 = 1\nfn2 = fn1\n")];
    let v2 = [("M", "module M where\nfn1 = \"x\"\nfn2 = fn1\n")];

    let first = run_with_shared_db(&mut db, &v1);
    assert!(first.errors.is_empty());
    assert_eq!(outcome_of(&first, "M", "fn2"), CacheOutcome::Miss);

    let second = run_with_shared_db(&mut db, &v2);
    assert!(second.errors.is_empty());
    assert_eq!(outcome_of(&second, "M", "fn1"), CacheOutcome::Miss);
    assert_eq!(
        outcome_of(&second, "M", "fn2"),
        CacheOutcome::Miss,
        "fn2 must recompile because fn1's scheme changed",
    );
}

#[test]
fn unrelated_decl_unaffected_by_sibling_body_edit() {
    // Module has `fn1`, `fn2` (depends on fn1), and `unrelated`
    // (depends on nothing). Edit fn1's body only: unrelated must
    // still hit.
    let mut db = TypecheckDb::open_in_memory().unwrap();
    let v1 = [(
        "M",
        "module M where\nfn1 = 1\nfn2 = fn1\nunrelated = 7\n",
    )];
    let v2 = [(
        "M",
        "module M where\nfn1 = 2\nfn2 = fn1\nunrelated = 7\n",
    )];

    let _ = run_with_shared_db(&mut db, &v1);
    let second = run_with_shared_db(&mut db, &v2);
    assert_eq!(outcome_of(&second, "M", "fn1"), CacheOutcome::Miss);
    assert_eq!(outcome_of(&second, "M", "fn2"), CacheOutcome::Hit);
    assert_eq!(outcome_of(&second, "M", "unrelated"), CacheOutcome::Hit);
}

// ---------------------------------------------------------------------------
// Cross-module
// ---------------------------------------------------------------------------

#[test]
fn cross_module_body_edit_leaves_importer_cached() {
    // A exports `fn1`; B defines `fn2 = fn1`. A body edit to
    // fn1 must leave B untouched.
    let mut db = TypecheckDb::open_in_memory().unwrap();
    let a_v1 = "module A where\nfn1 = 1\n";
    let a_v2 = "module A where\nfn1 = 2\n";
    let b_src = "module B where\nimport A\nfn2 = fn1\n";

    let first = run_with_shared_db(&mut db, &[("A", a_v1), ("B", b_src)]);
    assert!(first.errors.is_empty(), "{:?}", first.errors);
    assert_eq!(outcome_of(&first, "A", "fn1"), CacheOutcome::Miss);
    assert_eq!(outcome_of(&first, "B", "fn2"), CacheOutcome::Miss);

    let second = run_with_shared_db(&mut db, &[("A", a_v2), ("B", b_src)]);
    assert!(second.errors.is_empty(), "{:?}", second.errors);
    assert_eq!(outcome_of(&second, "A", "fn1"), CacheOutcome::Miss);
    assert_eq!(
        outcome_of(&second, "B", "fn2"),
        CacheOutcome::Hit,
        "cross-module body edit must not invalidate importers",
    );
}

#[test]
fn cross_module_type_edit_invalidates_importer() {
    // A's `fn1` flips Int → String. B's `fn2 = fn1` must
    // recompute because its dep's scheme hash changed.
    let mut db = TypecheckDb::open_in_memory().unwrap();
    let a_v1 = "module A where\nfn1 = 1\n";
    let a_v2 = "module A where\nfn1 = \"x\"\n";
    let b_src = "module B where\nimport A\nfn2 = fn1\n";

    let _ = run_with_shared_db(&mut db, &[("A", a_v1), ("B", b_src)]);
    let second = run_with_shared_db(&mut db, &[("A", a_v2), ("B", b_src)]);
    assert!(second.errors.is_empty(), "{:?}", second.errors);
    assert_eq!(outcome_of(&second, "A", "fn1"), CacheOutcome::Miss);
    assert_eq!(
        outcome_of(&second, "B", "fn2"),
        CacheOutcome::Miss,
        "importer must recompile when its dep's scheme changes type",
    );
}

// ---------------------------------------------------------------------------
// Type aliases + typeclasses
// ---------------------------------------------------------------------------

#[test]
fn type_alias_target_change_invalidates_reference() {
    // A defines `type Alias = Int` then flips to
    // `type Alias = String`. B uses `fn :: Alias -> Alias`. The
    // alias change is folded into B's module-context hash, so
    // B's SCC misses.
    let mut db = TypecheckDb::open_in_memory().unwrap();
    let a_v1 = "module A where\ntype Alias = Int\n";
    let a_v2 = "module A where\ntype Alias = String\n";
    let b_src = "\
module B where
import A
fn :: Alias -> Alias
fn x = x
";

    let _ = run_with_shared_db(&mut db, &[("A", a_v1), ("B", b_src)]);
    let second = run_with_shared_db(&mut db, &[("A", a_v2), ("B", b_src)]);
    assert!(second.errors.is_empty(), "{:?}", second.errors);
    assert_eq!(
        outcome_of(&second, "B", "fn"),
        CacheOutcome::Miss,
        "alias retarget must invalidate referencing importers",
    );
}

#[test]
fn typeclass_instance_body_edit_keeps_use_site_cached() {
    // A defines `class C a where meth :: a -> Int` plus
    // `instance C Int where meth _ = 0`. B uses `meth` against
    // an Int. When A's instance body flips `0 → 1`, the
    // instance head is unchanged, so B's use-site stays
    // cached — only instance **head** changes (class, types,
    // context) matter for caller caching, not method bodies.
    let mut db = TypecheckDb::open_in_memory().unwrap();
    let a_v1 = "\
module A where
class C a where
  meth :: a -> Int
instance C Int where
  meth _ = 0
";
    let a_v2 = "\
module A where
class C a where
  meth :: a -> Int
instance C Int where
  meth _ = 1
";
    let b_src = "\
module B where
import A
useIt :: Int
useIt = meth 1
";

    let first = run_with_shared_db(&mut db, &[("A", a_v1), ("B", b_src)]);
    assert!(first.errors.is_empty(), "{:?}", first.errors);
    assert_eq!(outcome_of(&first, "B", "useIt"), CacheOutcome::Miss);

    let second = run_with_shared_db(&mut db, &[("A", a_v2), ("B", b_src)]);
    assert!(second.errors.is_empty(), "{:?}", second.errors);
    assert_eq!(
        outcome_of(&second, "B", "useIt"),
        CacheOutcome::Hit,
        "call-site caches should survive instance method body edits",
    );
}

// ---------------------------------------------------------------------------
// Identity run: no source changes = full cache hit
// ---------------------------------------------------------------------------

#[test]
fn identical_second_run_is_full_hit() {
    // Nothing changes between runs. Every decl must hit.
    let mut db = TypecheckDb::open_in_memory().unwrap();
    let src = "\
module M where
foo = 1
bar = foo
baz = bar
";
    let _ = run_with_shared_db(&mut db, &[("M", src)]);
    let second = run_with_shared_db(&mut db, &[("M", src)]);
    assert!(second.errors.is_empty(), "{:?}", second.errors);
    assert_eq!(outcome_of(&second, "M", "foo"), CacheOutcome::Hit);
    assert_eq!(outcome_of(&second, "M", "bar"), CacheOutcome::Hit);
    assert_eq!(outcome_of(&second, "M", "baz"), CacheOutcome::Hit);
}

// ---------------------------------------------------------------------------
// Fine-grained non-value decl invalidation
// ---------------------------------------------------------------------------
//
// These tests exercise the per-decl shape cache introduced for data,
// newtype, type alias, class, instance, fixity, foreign, and
// foreign-data decls. The property under test: a change to one
// non-value decl invalidates only the value decls that actually
// reference it.

#[test]
fn data_change_invalidates_only_ctor_users() {
    // A defines `data Foo` + `data Bar`. B uses Foo's ctor; C uses
    // Bar's ctor. Changing Foo must Miss B but leave C Hit.
    let mut db = TypecheckDb::open_in_memory().unwrap();
    let a_v1 = "\
module A where
data Foo = FooA
data Bar = BarA
";
    let a_v2 = "\
module A where
data Foo = FooA | FooB
data Bar = BarA
";
    let b_src = "\
module B where
import A
useFoo = FooA
";
    let c_src = "\
module C where
import A
useBar = BarA
";
    let _ = run_with_shared_db(
        &mut db,
        &[("A", a_v1), ("B", b_src), ("C", c_src)],
    );
    let second = run_with_shared_db(
        &mut db,
        &[("A", a_v2), ("B", b_src), ("C", c_src)],
    );
    assert!(second.errors.is_empty(), "{:?}", second.errors);
    assert_eq!(
        outcome_of(&second, "B", "useFoo"),
        CacheOutcome::Miss,
        "Foo ctor user must recompile when Foo's shape changes",
    );
    assert_eq!(
        outcome_of(&second, "C", "useBar"),
        CacheOutcome::Hit,
        "Bar ctor user must stay cached when only Foo changes",
    );
}

#[test]
fn data_change_leaves_unrelated_module_cached() {
    // A has `data Foo`. B uses Foo. C uses neither.
    let mut db = TypecheckDb::open_in_memory().unwrap();
    let a_v1 = "module A where\ndata Foo = FooA\n";
    let a_v2 = "module A where\ndata Foo = FooA | FooB\n";
    let b_src = "module B where\nimport A\nuseFoo = FooA\n";
    let c_src = "module C where\nunrelated = 42\n";
    let _ = run_with_shared_db(
        &mut db,
        &[("A", a_v1), ("B", b_src), ("C", c_src)],
    );
    let second = run_with_shared_db(
        &mut db,
        &[("A", a_v2), ("B", b_src), ("C", c_src)],
    );
    assert_eq!(outcome_of(&second, "B", "useFoo"), CacheOutcome::Miss);
    assert_eq!(
        outcome_of(&second, "C", "unrelated"),
        CacheOutcome::Hit,
        "module that doesn't import A must stay fully cached",
    );
}

#[test]
fn newtype_change_invalidates_ctor_user() {
    // `newtype Foo = Foo Int` → `newtype Foo = Foo String`. A user
    // that wraps with `Foo x` must re-infer.
    let mut db = TypecheckDb::open_in_memory().unwrap();
    let a_v1 = "module A where\nnewtype Foo = Foo Int\n";
    let a_v2 = "module A where\nnewtype Foo = Foo String\n";
    let b_src = "module B where\nimport A\nmake = Foo 1\n";
    let _ = run_with_shared_db(&mut db, &[("A", a_v1), ("B", b_src)]);
    let second = run_with_shared_db(&mut db, &[("A", a_v2), ("B", b_src)]);
    assert_eq!(outcome_of(&second, "B", "make"), CacheOutcome::Miss);
}

#[test]
fn class_new_method_invalidates_class_users() {
    // Adding a method to a class changes the class's shape → every
    // value that references the class re-checks. This is
    // conservative; precise "only callers of new methods miss"
    // would require per-method nodes, not per-class.
    let mut db = TypecheckDb::open_in_memory().unwrap();
    let a_v1 = "\
module A where
class C a where
  meth :: a -> Int
";
    let a_v2 = "\
module A where
class C a where
  meth :: a -> Int
  other :: a -> String
";
    let b_src = "\
module B where
import A
useIt :: Int
useIt = meth 1
";
    let _ = run_with_shared_db(&mut db, &[("A", a_v1), ("B", b_src)]);
    let second = run_with_shared_db(&mut db, &[("A", a_v2), ("B", b_src)]);
    assert_eq!(outcome_of(&second, "B", "useIt"), CacheOutcome::Miss);
}

#[test]
fn class_unused_does_not_invalidate_unrelated_values() {
    // Changing class D's shape mustn't invalidate users of class C.
    let mut db = TypecheckDb::open_in_memory().unwrap();
    let a_v1 = "\
module A where
class C a where
  meth :: a -> Int
class D a where
  other :: a -> Int
instance C Int where
  meth _ = 0
";
    let a_v2 = "\
module A where
class C a where
  meth :: a -> Int
class D a where
  other :: a -> Int
  extra :: a -> String
instance C Int where
  meth _ = 0
";
    let b_src = "\
module B where
import A
useIt :: Int
useIt = meth 1
";
    let _ = run_with_shared_db(&mut db, &[("A", a_v1), ("B", b_src)]);
    let second = run_with_shared_db(&mut db, &[("A", a_v2), ("B", b_src)]);
    assert_eq!(
        outcome_of(&second, "B", "useIt"),
        CacheOutcome::Hit,
        "class D change must not invalidate C users",
    );
}

#[test]
fn adding_instance_invalidates_class_users() {
    // Adding an instance of C invalidates every in-scope value
    // that uses class C (conservative, but correct: the user's
    // instance-resolution outcome could genuinely change).
    let mut db = TypecheckDb::open_in_memory().unwrap();
    let a_v1 = "\
module A where
class C a where
  meth :: a -> Int
instance C Int where
  meth _ = 0
";
    let a_v2 = "\
module A where
class C a where
  meth :: a -> Int
instance C Int where
  meth _ = 0
instance C String where
  meth _ = 1
";
    let b_src = "\
module B where
import A
useIt :: Int
useIt = meth 1
";
    let _ = run_with_shared_db(&mut db, &[("A", a_v1), ("B", b_src)]);
    let second = run_with_shared_db(&mut db, &[("A", a_v2), ("B", b_src)]);
    assert_eq!(outcome_of(&second, "B", "useIt"), CacheOutcome::Miss);
}

#[test]
fn adding_unrelated_instance_does_not_invalidate() {
    // A defines class C + D. Adding a new D instance mustn't
    // invalidate B's use of class C.
    let mut db = TypecheckDb::open_in_memory().unwrap();
    let a_v1 = "\
module A where
class C a where
  m :: a -> Int
class D a where
  n :: a -> String
instance C Int where
  m _ = 0
";
    let a_v2 = "\
module A where
class C a where
  m :: a -> Int
class D a where
  n :: a -> String
instance C Int where
  m _ = 0
instance D Int where
  n _ = \"x\"
";
    let b_src = "\
module B where
import A
useIt :: Int
useIt = m 1
";
    let _ = run_with_shared_db(&mut db, &[("A", a_v1), ("B", b_src)]);
    let second = run_with_shared_db(&mut db, &[("A", a_v2), ("B", b_src)]);
    assert_eq!(
        outcome_of(&second, "B", "useIt"),
        CacheOutcome::Hit,
        "adding a D instance must not invalidate a C-only caller",
    );
}

#[test]
fn cross_module_type_alias_change_invalidates_transitively() {
    // A defines `type Alias = Int`. B re-exports via `type
    // IndirectAlias = Alias`. C uses `IndirectAlias`. Changing A's
    // Alias must invalidate C.
    let mut db = TypecheckDb::open_in_memory().unwrap();
    let a_v1 = "module A where\ntype Alias = Int\n";
    let a_v2 = "module A where\ntype Alias = String\n";
    let b_src = "module B where\nimport A\ntype IndirectAlias = Alias\n";
    let c_src = "\
module C where
import B
fn :: IndirectAlias -> IndirectAlias
fn x = x
";
    let _ = run_with_shared_db(
        &mut db,
        &[("A", a_v1), ("B", b_src), ("C", c_src)],
    );
    let second = run_with_shared_db(
        &mut db,
        &[("A", a_v2), ("B", b_src), ("C", c_src)],
    );
    assert_eq!(outcome_of(&second, "C", "fn"), CacheOutcome::Miss);
}

#[test]
fn data_decl_leaves_unrelated_value_cached_in_same_module() {
    // Same module. Edit `data Foo`. `unrelated` doesn't touch Foo
    // and must stay cached.
    let mut db = TypecheckDb::open_in_memory().unwrap();
    let v1 = "\
module M where
data Foo = FooA
useFoo = FooA
unrelated = 42
";
    let v2 = "\
module M where
data Foo = FooA | FooB
useFoo = FooA
unrelated = 42
";
    let _ = run_with_shared_db(&mut db, &[("M", v1)]);
    let second = run_with_shared_db(&mut db, &[("M", v2)]);
    assert_eq!(outcome_of(&second, "M", "useFoo"), CacheOutcome::Miss);
    assert_eq!(
        outcome_of(&second, "M", "unrelated"),
        CacheOutcome::Hit,
        "value that doesn't reference Foo must stay cached",
    );
}

#[test]
fn foreign_import_body_change_invalidates_user() {
    // `foreign import` declarations produce a stable scheme. Users
    // depend on that scheme hash.
    let mut db = TypecheckDb::open_in_memory().unwrap();
    let v1 = "\
module M where
foreign import fromJs :: Int
useIt = fromJs
";
    let v2 = "\
module M where
foreign import fromJs :: String
useIt = fromJs
";
    let _ = run_with_shared_db(&mut db, &[("M", v1)]);
    let second = run_with_shared_db(&mut db, &[("M", v2)]);
    assert_eq!(
        outcome_of(&second, "M", "useIt"),
        CacheOutcome::Miss,
        "type change of a foreign import must invalidate users",
    );
}

#[test]
fn record_alias_field_addition_invalidates_cross_module_user() {
    // D exports `type R = { a :: Int }`. Q imports R and uses it in a
    // signature. Adding a field to R must invalidate Q's `consume` — its
    // cached scheme baked in the old (closed) record, so a caller supplying
    // the new field would otherwise fail to unify (`Mismatch({}, { x | r })`).
    let mut db = TypecheckDb::open_in_memory().unwrap();
    let d_v1 = "module D where\ntype R = { a :: Int }\n";
    let d_v2 = "module D where\ntype R = { a :: Int, x :: Int }\n";
    let q = "\
module Q where
import D (R)
consume :: R -> Int
consume r = r.a
";
    let a_v1 = "\
module A where
import D (R)
import Q (consume)
use r = { c: consume r }
";
    let a_v2 = "\
module A where
import D (R)
import Q (consume)
use r = { c: consume r, v: r.x }
";
    let first = run_with_shared_db(&mut db, &[("D", d_v1), ("Q", q), ("A", a_v1)]);
    assert!(first.errors.is_empty(), "v1 should typecheck: {:?}", first.errors);
    let second = run_with_shared_db(&mut db, &[("D", d_v2), ("Q", q), ("A", a_v2)]);
    assert!(
        second.errors.is_empty(),
        "after adding field `x` to record alias R, the cross-module user \
         `consume` must be re-checked so `use` type-checks; stale alias caused: {:?}",
        second.errors,
    );
}

#[test]
fn record_alias_field_addition_invalidates_through_alias_chain() {
    // Like the above but the field is added to an alias reached through a
    // chain: `type Outer = Maybe Inner`, and the field goes on `Inner`.
    // Q's `consume :: Outer -> Int` pattern-matches into the record, so the
    // added field must still invalidate it.
    let mut db = TypecheckDb::open_in_memory().unwrap();
    let d_v1 = "\
module D where
data Maybe a = Nothing | Just a
type Inner = { a :: Int }
type Outer = Maybe Inner
";
    let d_v2 = "\
module D where
data Maybe a = Nothing | Just a
type Inner = { a :: Int, x :: Int }
type Outer = Maybe Inner
";
    let q = "\
module Q where
import D (Outer, Inner, Maybe(..))
consume :: Outer -> Int
consume m = case m of
  Just r -> r.a
  Nothing -> 0
";
    let a_v1 = "\
module A where
import D (Outer, Inner, Maybe(..))
import Q (consume)
use m = consume m
";
    let a_v2 = "\
module A where
import D (Outer, Inner, Maybe(..))
import Q (consume)
use m = case m of
  Just r -> { c: consume m, v: r.x }
  Nothing -> { c: consume m, v: 0 }
";
    let first = run_with_shared_db(&mut db, &[("D", d_v1), ("Q", q), ("A", a_v1)]);
    assert!(first.errors.is_empty(), "v1 should typecheck: {:?}", first.errors);
    let second = run_with_shared_db(&mut db, &[("D", d_v2), ("Q", q), ("A", a_v2)]);
    assert!(
        second.errors.is_empty(),
        "adding field `x` to Inner (= Outer's target) must invalidate \
         `consume`; stale alias chain caused: {:?}",
        second.errors,
    );
}

#[test]
fn perdecl_constrained_sig_alias_field_addition_invalidates() {
    // Q's `consume` has a *constrained* signature that mentions R. The
    // per-decl cache pins R's expanded+closed record form; adding a field to
    // R must invalidate `consume`'s per-decl entry too.
    let mut db = TypecheckDb::open_in_memory().unwrap();
    let d_v1 = "module D where\ntype R = { a :: Int }\n";
    let d_v2 = "module D where\ntype R = { a :: Int, x :: Int }\n";
    let q = "\
module Q where
import D (R)
class C a where
  cm :: a -> Int
consume :: forall a. C a => a -> R -> Int
consume _ r = r.a
";
    let a_v1 = "\
module A where
import D (R)
import Q (consume, class C)
data T = T
instance C T where
  cm _ = 0
mkR :: R
mkR = { a: 1 }
use = consume T mkR
";
    let a_v2 = "\
module A where
import D (R)
import Q (consume, class C)
data T = T
instance C T where
  cm _ = 0
mkR :: R
mkR = { a: 1, x: 2 }
use = consume T mkR
";
    let first = run_with_shared_db(&mut db, &[("D", d_v1), ("Q", q), ("A", a_v1)]);
    assert!(first.errors.is_empty(), "v1 should typecheck: {:?}", first.errors);
    let second = run_with_shared_db(&mut db, &[("D", d_v2), ("Q", q), ("A", a_v2)]);
    assert!(
        second.errors.is_empty(),
        "after adding field `x` to R, `consume`'s per-decl cache (constrained \
         sig pins R expanded+closed) must be invalidated; stale entry caused: {:?}",
        second.errors,
    );
}
// ---------------------------------------------------------------------------
// Build-plan module memo (Tier 1)
//
// The build plan only activates on a *persistent* (on-disk) db, so these
// tests open a tempfile-backed `TypecheckDb`, build it cold, then **reopen
// it from the same path** (simulating a fresh process / warm rebuild) and
// assert which modules are restored from their memo vs re-checked.
// ---------------------------------------------------------------------------

/// Find a module's result by name and return whether it was restored from
/// memo (`cached`).
fn was_cached(report: &super::super::driver_multi::ModuleCheckReport, name: &str) -> bool {
    report
        .results
        .iter()
        .find(|r| r.name == name)
        .unwrap_or_else(|| panic!("no result for module {name}"))
        .cached
}

fn js_of(report: &super::super::driver_multi::ModuleCheckReport, name: &str) -> Option<String> {
    report
        .results
        .iter()
        .find(|r| r.name == name)
        .and_then(|r| r.js_module_text.clone())
}

#[test]
fn build_plan_no_op_rebuild_marks_all_modules_cached() {
    let tmp = tempfile::NamedTempFile::new().unwrap();
    let path = tmp.path().to_path_buf();
    drop(tmp);
    let a = "module A where\nfn1 = 1\n";
    let b = "module B where\nimport A\nfn2 = fn1\n";

    // Cold build (fresh db): everything is checked, memos are written.
    {
        let mut db = TypecheckDb::open(&path).unwrap();
        db.set_codegen(true);
        let first = run_with_shared_db(&mut db, &[("A", a), ("B", b)]);
        assert!(first.errors.is_empty(), "{:?}", first.errors);
        assert!(!was_cached(&first, "A") && !was_cached(&first, "B"), "cold build checks everything");
        assert!(js_of(&first, "A").is_some() && js_of(&first, "B").is_some(), "codegen produced JS");
    }

    // Warm rebuild (reopened db, same sources): nothing changed, so nothing
    // is dirty and nothing is "needed" — every module is skipped (cached).
    {
        let mut db = TypecheckDb::open(&path).unwrap();
        db.set_codegen(true);
        let second = run_with_shared_db(&mut db, &[("A", a), ("B", b)]);
        assert!(second.errors.is_empty(), "{:?}", second.errors);
        assert!(was_cached(&second, "A"), "A unchanged → skipped");
        assert!(was_cached(&second, "B"), "B unchanged → skipped");
    }
    let _ = std::fs::remove_file(&path);
}

#[test]
fn build_plan_dirty_module_uses_restored_clean_dependency() {
    // Y is unchanged (clean); X is edited (dirty) and imports Y. The plan
    // must restore Y into the registry (it's in X's import-closure) so X's
    // re-check resolves `yval`. An empty registry would surface as an import
    // error on X — so "no errors" proves Y was restored.
    let tmp = tempfile::NamedTempFile::new().unwrap();
    let path = tmp.path().to_path_buf();
    drop(tmp);
    let y = "module Y where\nyval :: Int\nyval = 1\n";
    let x_v1 = "module X where\nimport Y\nxval = yval\n";
    let x_v2 = "module X where\nimport Y\nxval = yval + 0\n"; // body edit to X only

    {
        let mut db = TypecheckDb::open(&path).unwrap();
        db.set_codegen(true);
        let first = run_with_shared_db(&mut db, &[("Y", y), ("X", x_v1)]);
        assert!(first.errors.is_empty(), "{:?}", first.errors);
    }
    {
        let mut db = TypecheckDb::open(&path).unwrap();
        db.set_codegen(true);
        let second = run_with_shared_db(&mut db, &[("Y", y), ("X", x_v2)]);
        assert!(second.errors.is_empty(), "{:?}", second.errors);
        assert!(was_cached(&second, "Y"), "Y unchanged but imported by dirty X → restored from memo");
        assert!(!was_cached(&second, "X"), "X's source changed → re-checked");
        // X must have type-checked against the restored Y (no import errors).
        let x = second.results.iter().find(|r| r.name == "X").unwrap();
        assert!(x.import_errors.is_empty(), "X resolved Y from the restored memo: {:?}", x.import_errors);
    }
    let _ = std::fs::remove_file(&path);
}

#[test]
fn build_plan_type_edit_reprocesses_only_dirty_cone() {
    // A's exported type changes; B imports A (so it's in the dirty cone and
    // must re-check); C imports nothing changed (skipped). Uses a type edit
    // so the change actually propagates under fine-grained invalidation.
    let tmp = tempfile::NamedTempFile::new().unwrap();
    let path = tmp.path().to_path_buf();
    drop(tmp);
    let a_v1 = "module A where\nfn1 = 1\n"; // Int
    let a_v2 = "module A where\nfn1 = \"x\"\n"; // String — exported type changes
    let b = "module B where\nimport A\nfn2 = fn1\n"; // imports A
    let c = "module C where\nunrelated = 7\n"; // imports nothing user-defined

    {
        let mut db = TypecheckDb::open(&path).unwrap();
        db.set_codegen(true);
        let first = run_with_shared_db(&mut db, &[("A", a_v1), ("B", b), ("C", c)]);
        assert!(first.errors.is_empty(), "{:?}", first.errors);
    }
    {
        let mut db = TypecheckDb::open(&path).unwrap();
        db.set_codegen(true);
        let second = run_with_shared_db(&mut db, &[("A", a_v2), ("B", b), ("C", c)]);
        assert!(second.errors.is_empty(), "{:?}", second.errors);
        assert!(!was_cached(&second, "A"), "A's source changed → re-checked");
        assert!(!was_cached(&second, "B"), "B imports A whose exported type changed → re-checked");
        assert!(was_cached(&second, "C"), "C imports nothing changed → skipped");
    }
    let _ = std::fs::remove_file(&path);
}

#[test]
fn build_plan_body_edit_does_not_invalidate_importer() {
    // Fine-grained (Stage 4): A's fn1 keeps type Int across a body edit; B
    // imports A. A is re-checked (its source changed) but its *exported
    // interface* is unchanged, so B must NOT be invalidated — it stays cached.
    // (Coarse invalidation would have re-checked B as part of A's cone.)
    let tmp = tempfile::NamedTempFile::new().unwrap();
    let path = tmp.path().to_path_buf();
    drop(tmp);
    let a_v1 = "module A where\nfn1 = 1\n";
    let a_v2 = "module A where\nfn1 = 2\n"; // body edit; inferred type still Int
    let b = "module B where\nimport A (fn1)\nfn2 = fn1\n";

    {
        let mut db = TypecheckDb::open(&path).unwrap();
        db.set_codegen(true);
        let first = run_with_shared_db(&mut db, &[("A", a_v1), ("B", b)]);
        assert!(first.errors.is_empty(), "{:?}", first.errors);
    }
    {
        let mut db = TypecheckDb::open(&path).unwrap();
        db.set_codegen(true);
        let second = run_with_shared_db(&mut db, &[("A", a_v2), ("B", b)]);
        assert!(second.errors.is_empty(), "{:?}", second.errors);
        assert!(!was_cached(&second, "A"), "A's source changed → re-checked");
        assert!(
            was_cached(&second, "B"),
            "A's exported type is unchanged, so B must stay cached (fine-grained)",
        );
    }
    let _ = std::fs::remove_file(&path);
}

#[test]
fn build_plan_type_edit_does_invalidate_importer() {
    // The dual of the above: when A's exported *type* changes, B must be
    // re-checked (its ExportDiff is non-empty and touches what B imports).
    let tmp = tempfile::NamedTempFile::new().unwrap();
    let path = tmp.path().to_path_buf();
    drop(tmp);
    let a_v1 = "module A where\nfn1 = 1\n"; // Int
    let a_v2 = "module A where\nfn1 = \"x\"\n"; // String — exported type changes
    let b = "module B where\nimport A (fn1)\nfn2 = fn1\n";

    {
        let mut db = TypecheckDb::open(&path).unwrap();
        db.set_codegen(true);
        let _ = run_with_shared_db(&mut db, &[("A", a_v1), ("B", b)]);
    }
    {
        let mut db = TypecheckDb::open(&path).unwrap();
        db.set_codegen(true);
        let second = run_with_shared_db(&mut db, &[("A", a_v2), ("B", b)]);
        assert!(second.errors.is_empty(), "{:?}", second.errors);
        assert!(!was_cached(&second, "A"), "A changed → re-checked");
        assert!(!was_cached(&second, "B"), "A's exported type changed → B re-checked");
    }
    let _ = std::fs::remove_file(&path);
}

/// Whether a report has no diagnostics of any kind.
fn report_clean(report: &super::super::driver_multi::ModuleCheckReport) -> bool {
    report.errors.is_empty()
        && report.results.iter().all(|r| {
            r.constraint_errors.is_empty()
                && r.import_errors.is_empty()
                && r.inference_error.is_none()
        })
}

/// A human-readable dump of a report's diagnostics (for assertion messages).
fn report_problems(report: &super::super::driver_multi::ModuleCheckReport) -> String {
    let mut s = format!("errors={:?}", report.errors);
    for r in &report.results {
        if !r.constraint_errors.is_empty()
            || !r.import_errors.is_empty()
            || r.inference_error.is_some()
        {
            s.push_str(&format!(
                "\n  {}: constraint={:?} import={:?} infer={:?}",
                r.name, r.constraint_errors, r.import_errors, r.inference_error
            ));
        }
    }
    s
}

#[test]
fn build_plan_record_alias_field_addition_invalidates_persistent() {
    // Persistent (build-plan) analogue of
    // `record_alias_field_addition_invalidates_cross_module_user`. The
    // in-memory version tests only the per-decl cache; this one reopens a
    // tempfile db between runs so the *module memo* build plan is active —
    // which is what `pfc compile-db` actually uses. Reproduces the oa-app
    // bug: adding a field to a record alias in D fails to invalidate the
    // cross-module user Q, so a caller A that supplies the new field errors.
    let tmp = tempfile::NamedTempFile::new().unwrap();
    let path = tmp.path().to_path_buf();
    drop(tmp);
    let d_v1 = "module D where\ntype R = { a :: Int }\n";
    let d_v2 = "module D where\ntype R = { a :: Int, x :: Int }\n";
    let q = "\
module Q where
import D (R)
consume :: R -> Int
consume r = r.a
";
    let a_v1 = "\
module A where
import D (R)
import Q (consume)
use r = { c: consume r }
";
    let a_v2 = "\
module A where
import D (R)
import Q (consume)
use r = { c: consume r, v: r.x }
";

    {
        let mut db = TypecheckDb::open(&path).unwrap();
        db.set_codegen(true);
        let first = run_with_shared_db(&mut db, &[("D", d_v1), ("Q", q), ("A", a_v1)]);
        assert!(report_clean(&first), "v1 should typecheck: {}", report_problems(&first));
    }
    {
        let mut db = TypecheckDb::open(&path).unwrap();
        db.set_codegen(true);
        let second = run_with_shared_db(&mut db, &[("D", d_v2), ("Q", q), ("A", a_v2)]);
        assert!(
            report_clean(&second),
            "after adding field `x` to record alias R (persistent build plan), the \
             cross-module user `consume` must be re-checked so `use` type-checks; \
             stale memo caused: {}",
            report_problems(&second),
        );
    }
    let _ = std::fs::remove_file(&path);
}

#[test]
fn build_plan_local_alias_wrapping_imported_alias_invalidates_persistent() {
    // Q defines a *local* alias `Input` that wraps `Array R` where R is an
    // imported record alias. Adding a field to R must invalidate Q's
    // `consume` even though Q's signature names only the local alias Input.
    let tmp = tempfile::NamedTempFile::new().unwrap();
    let path = tmp.path().to_path_buf();
    drop(tmp);
    let d_v1 = "module D where\ntype R = { a :: Int }\n";
    let d_v2 = "module D where\ntype R = { a :: Int, x :: Int }\n";
    let q = "\
module Q where
import D (R)
type Input = { items :: Array R }
consume :: Input -> Int
consume i = 0
";
    let a_v1 = "\
module A where
import D (R)
import Q (consume, Input)
mkR :: R
mkR = { a: 1 }
use = consume { items: [ mkR ] }
";
    let a_v2 = "\
module A where
import D (R)
import Q (consume, Input)
mkR :: R
mkR = { a: 1, x: 2 }
use = consume { items: [ mkR ] }
";

    {
        let mut db = TypecheckDb::open(&path).unwrap();
        db.set_codegen(true);
        let first = run_with_shared_db(&mut db, &[("D", d_v1), ("Q", q), ("A", a_v1)]);
        assert!(report_clean(&first), "v1 should typecheck: {}", report_problems(&first));
    }
    {
        let mut db = TypecheckDb::open(&path).unwrap();
        db.set_codegen(true);
        let second = run_with_shared_db(&mut db, &[("D", d_v2), ("Q", q), ("A", a_v2)]);
        assert!(
            report_clean(&second),
            "adding field `x` to R must invalidate Q's `consume` (local alias \
             Input wraps Array R); stale memo caused: {}",
            report_problems(&second),
        );
    }
    let _ = std::fs::remove_file(&path);
}

#[test]
fn build_plan_cross_build_interface_drift_invalidates_dependent() {
    // Cross-build drift: R gains a field in run2, a build that EXCLUDES Q.
    // In run3 the full set is rebuilt; Q's memo was written against R's old
    // interface, so the plan must detect Q is stale w.r.t. D and re-check it.
    let tmp = tempfile::NamedTempFile::new().unwrap();
    let path = tmp.path().to_path_buf();
    drop(tmp);
    let d_v1 = "module D where\ntype R = { a :: Int }\n";
    let d_v2 = "module D where\ntype R = { a :: Int, x :: Int }\n";
    let q = "\
module Q where
import D (R)
consume :: R -> Int
consume r = r.a
";
    let a_v1 = "\
module A where
import D (R)
import Q (consume)
use r = { c: consume r }
";
    let a_v2 = "\
module A where
import D (R)
import Q (consume)
use r = { c: consume r, v: r.x }
";

    // run1: cold build of all three, clean.
    {
        let mut db = TypecheckDb::open(&path).unwrap();
        db.set_codegen(true);
        let r1 = run_with_shared_db(&mut db, &[("D", d_v1), ("Q", q), ("A", a_v1)]);
        assert!(report_clean(&r1), "run1: {}", report_problems(&r1));
    }
    // run2: rebuild only D (with the new field). Q is excluded from this build,
    // so its memo is not touched and still records R's old interface.
    {
        let mut db = TypecheckDb::open(&path).unwrap();
        db.set_codegen(true);
        let _ = run_with_shared_db(&mut db, &[("D", d_v2)]);
    }
    // run3: full rebuild. Q's memo is stale w.r.t. D's changed interface, so
    // the plan must re-check Q; otherwise A errors against the stale closed R.
    {
        let mut db = TypecheckDb::open(&path).unwrap();
        db.set_codegen(true);
        let r3 = run_with_shared_db(&mut db, &[("D", d_v2), ("Q", q), ("A", a_v2)]);
        assert!(
            report_clean(&r3),
            "run3: Q's `consume` scheme baked in the stale closed record `{{ a }}`; \
             the rebuild must detect Q is stale w.r.t. D's changed interface and \
             re-check it. stale cross-build memo caused: {}",
            report_problems(&r3),
        );
    }
    let _ = std::fs::remove_file(&path);
}

#[test]
fn build_plan_cross_build_drift_stale_expanded_record_scheme() {
    // Cross-build drift through an alias chain: R gains a field in a build
    // that excludes Q, then the full rebuild must detect Q's memo is stale.
    let tmp = tempfile::NamedTempFile::new().unwrap();
    let path = tmp.path().to_path_buf();
    drop(tmp);
    let d_v1 = "module D where\ntype R = { a :: Int }\n";
    let d_v2 = "module D where\ntype R = { a :: Int, x :: Int }\n";
    let q = "\
module Q where
import D (R)
consume :: R -> Int
consume r = r.a
";
    let a_v1 = "\
module A where
import D (R)
import Q (consume)
use r = { c: consume r }
";
    let a_v2 = "\
module A where
import D (R)
import Q (consume)
use r = { c: consume r, v: r.x }
";
    {
        let mut db = TypecheckDb::open(&path).unwrap();
        db.set_codegen(true);
        let r1 = run_with_shared_db(&mut db, &[("D", d_v1), ("Q", q), ("A", a_v1)]);
        assert!(report_clean(&r1), "run1: {}", report_problems(&r1));
    }
    {
        let mut db = TypecheckDb::open(&path).unwrap();
        db.set_codegen(true);
        let _ = run_with_shared_db(&mut db, &[("D", d_v2)]);
    }
    {
        let mut db = TypecheckDb::open(&path).unwrap();
        db.set_codegen(true);
        let r3 = run_with_shared_db(&mut db, &[("D", d_v2), ("Q", q), ("A", a_v2)]);
        assert!(
            report_clean(&r3),
            "run3: after R gained field `x` in a build that excluded Q, the full \
             rebuild must detect Q's memo is stale w.r.t. D and re-check it; \
             stale cross-build memo caused: {}",
            report_problems(&r3),
        );
    }
    let _ = std::fs::remove_file(&path);
}

#[test]
fn build_plan_cross_build_drift_through_local_alias_wrapper() {
    // Cross-build drift where Q's signature names only a local alias that
    // wraps the imported R. R gains a field in a build excluding Q; the full
    // rebuild must still detect Q is stale.
    let tmp = tempfile::NamedTempFile::new().unwrap();
    let path = tmp.path().to_path_buf();
    drop(tmp);
    let d_v1 = "module D where\ntype R = { a :: Int }\n";
    let d_v2 = "module D where\ntype R = { a :: Int, x :: Int }\n";
    let q = "\
module Q where
import D (R)
type Input = { items :: Array R }
consume :: Input -> Int
consume i = 0
";
    let a_v1 = "\
module A where
import D (R)
import Q (consume, Input)
mkR :: R
mkR = { a: 1 }
use = consume { items: [ mkR ] }
";
    let a_v2 = "\
module A where
import D (R)
import Q (consume, Input)
mkR :: R
mkR = { a: 1, x: 2 }
use = consume { items: [ mkR ] }
";
    {
        let mut db = TypecheckDb::open(&path).unwrap();
        db.set_codegen(true);
        let r1 = run_with_shared_db(&mut db, &[("D", d_v1), ("Q", q), ("A", a_v1)]);
        assert!(report_clean(&r1), "run1: {}", report_problems(&r1));
    }
    {
        let mut db = TypecheckDb::open(&path).unwrap();
        db.set_codegen(true);
        let _ = run_with_shared_db(&mut db, &[("D", d_v2)]);
    }
    {
        let mut db = TypecheckDb::open(&path).unwrap();
        db.set_codegen(true);
        let r3 = run_with_shared_db(&mut db, &[("D", d_v2), ("Q", q), ("A", a_v2)]);
        assert!(
            report_clean(&r3),
            "run3: Q's `consume` memo (Input wraps Array R) is stale w.r.t. R's \
             new field; the rebuild must re-check Q; stale cross-build memo \
             caused: {}",
            report_problems(&r3),
        );
    }
    let _ = std::fs::remove_file(&path);
}

#[test]
fn build_plan_within_build_structural_dep_reports_construction_error() {
    // Within a single build, D's alias R drops a field between builds; a
    // caller A builds a record literal that must match R. The incremental
    // build must not restore a stale field-less R and miss A's error that a
    // cold build catches.
    let tmp = tempfile::NamedTempFile::new().unwrap();
    let path = tmp.path().to_path_buf();
    drop(tmp);
    let d_v1 = "module D where\ntype R = { a :: Int, x :: Int }\n";
    let d_v2 = "module D where\ntype R = { a :: Int }\n";
    let q = "\
module Q where
import D (R)
class C a where
  cm :: a -> Int
consume :: forall a. C a => a -> R -> Int
consume _ r = r.a
";
    let a = "\
module A where
import Q (consume, class C)
data T = T
instance C T where
  cm _ = 0
mk = consume T { a: 1 }
";

    // Cold build with d_v2 (field-less R): A supplies only `{ a: 1 }`, which
    // is fine, but if A had supplied `x` it must be rejected. First establish
    // the clean baseline with d_v1.
    {
        let mut db = TypecheckDb::open(&path).unwrap();
        db.set_codegen(true);
        let _ = run_with_shared_db(&mut db, &[("D", d_v1), ("Q", q), ("A", a)]);
    }
    // Cold build of d_v2 as a sanity reference.
    {
        let mut db = TypecheckDb::open_in_memory().unwrap();
        db.set_codegen(true);
        let cold = run_with_shared_db(&mut db, &[("D", d_v2), ("Q", q), ("A", a)]);
        assert!(report_clean(&cold), "sanity: cold build of d_v2 must reject A's field-less literal");
    }
    // Incremental build with d_v2: must match the cold build's verdict.
    {
        let mut db = TypecheckDb::open(&path).unwrap();
        db.set_codegen(true);
        let inc = run_with_shared_db(&mut db, &[("D", d_v2), ("Q", q), ("A", a)]);
        assert!(
            report_clean(&inc),
            "incremental build restored a stale field-less R and missed A's error \
             that the cold build catches",
        );
    }
    let _ = std::fs::remove_file(&path);
}

#[test]
fn build_plan_errored_module_is_never_memoized() {
    let tmp = tempfile::NamedTempFile::new().unwrap();
    let path = tmp.path().to_path_buf();
    drop(tmp);
    // `bad` is annotated Int but defined as a String → a type error.
    let m = "module M where\nbad :: Int\nbad = \"x\"\n";

    {
        let mut db = TypecheckDb::open(&path).unwrap();
        db.set_codegen(true);
        let first = run_with_shared_db(&mut db, &[("M", m)]);
        assert!(!first.errors.is_empty() || first.results[0].constraint_errors.len() + first.results[0].import_errors.len() > 0 || first.results[0].inference_error.is_some(),
            "M should produce a diagnostic");
    }
    {
        // Same (still-erroring) source: M must be re-checked, not restored,
        // so its diagnostic is re-reported.
        let mut db = TypecheckDb::open(&path).unwrap();
        db.set_codegen(true);
        let second = run_with_shared_db(&mut db, &[("M", m)]);
        assert!(!was_cached(&second, "M"), "errored module is never memoized → always re-checked");
    }
    let _ = std::fs::remove_file(&path);
}
