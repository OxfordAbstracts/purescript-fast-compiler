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
