//! Incremental-caching tests for the per-declaration codegen (`DeclDb` engine).
//!
//! These assert that a declaration's generated JS is only recomputed when its
//! inputs actually change: editing one decl's body must not re-codegen its
//! peers, a type change must invalidate users, an instance change must
//! invalidate the decls whose dictionaries it feeds, etc.
//!
//! Unlike `codegen_decldb.rs` these don't run Node — they drive the same module
//! set through a SHARED `TypecheckDb` twice and inspect `codegen_outcomes`
//! (Hit/Miss per codegen decl-key) on the second run.

use purescript_fast_compiler::parse;
use purescript_fast_compiler::typecheck_db::driver_multi::{
    check_many_modules_with_db, ModuleCheckReport, ModuleInput,
};
use purescript_fast_compiler::typecheck_db::{CacheOutcome, TypecheckDb};

fn extract_module_name(source: &str) -> String {
    for line in source.lines() {
        let t = line.trim();
        if let Some(rest) = t.strip_prefix("module ") {
            if let Some(name) = rest.split_whitespace().next() {
                return name.to_string();
            }
        }
    }
    "Main".to_string()
}

/// Run a set of `(module_name, source)` modules through `db` with codegen on.
fn run(db: &mut TypecheckDb, sources: &[(&str, &str)]) -> ModuleCheckReport {
    let inputs: Vec<ModuleInput> = sources
        .iter()
        .map(|(name, src)| {
            let cst = parse(src).expect("parse failed");
            ModuleInput::new(name.to_string(), src.to_string(), cst)
        })
        .collect();
    let report = check_many_modules_with_db(db, inputs);
    assert!(
        report.errors.is_empty(),
        "multi-module errors: {:?}",
        report.errors
    );
    report
}

/// Convenience overload: each source carries its own `module X where`.
fn run_named<'a>(db: &mut TypecheckDb, sources: &[&'a str]) -> ModuleCheckReport {
    let named: Vec<(String, &'a str)> =
        sources.iter().map(|s| (extract_module_name(s), *s)).collect();
    let refs: Vec<(&str, &str)> =
        named.iter().map(|(n, s)| (n.as_str(), *s)).collect();
    run(db, &refs)
}

fn outcome(report: &ModuleCheckReport, module: &str, key: &str) -> CacheOutcome {
    let result = report
        .results
        .iter()
        .find(|r| r.name == module)
        .unwrap_or_else(|| {
            panic!(
                "module {module:?} not in report; present: {:?}",
                report.results.iter().map(|r| &r.name).collect::<Vec<_>>()
            )
        });
    *result.codegen_outcomes.get(key).unwrap_or_else(|| {
        panic!(
            "codegen key {key:?} not in {module:?}; present: {:?}",
            result.codegen_outcomes.keys().collect::<Vec<_>>()
        )
    })
}

fn new_db() -> TypecheckDb {
    let mut db = TypecheckDb::open_in_memory().expect("in-memory db");
    db.set_codegen(true);
    db
}

/// All instance/derive codegen outcomes (keys start with `i__`) for a module.
fn instance_outcomes(report: &ModuleCheckReport, module: &str) -> Vec<CacheOutcome> {
    let result = report
        .results
        .iter()
        .find(|r| r.name == module)
        .expect("module present");
    let mut out: Vec<CacheOutcome> = result
        .codegen_outcomes
        .iter()
        .filter(|(k, _)| k.starts_with("i__"))
        .map(|(_, v)| *v)
        .collect();
    out.sort_by_key(|o| matches!(o, CacheOutcome::Miss));
    out
}

fn count_miss(outcomes: &[CacheOutcome]) -> usize {
    outcomes.iter().filter(|o| matches!(o, CacheOutcome::Miss)).count()
}

fn count_hit(outcomes: &[CacheOutcome]) -> usize {
    outcomes.iter().filter(|o| matches!(o, CacheOutcome::Hit)).count()
}

// ===========================================================================
// Chapter 6 scenarios — book.purescript.org/chapter6
//   - instance dependencies   (constrained instances: Show a => Show (Box a))
//   - multi-parameter classes  (class Convert a b)
//   - superclasses             (class Eq a <= Ord a)
// All use locally-declared classes (the incremental harness has no Prelude).
// Each test reasons about exactly which declarations SHOULD rebuild.
// ===========================================================================

// --- instance dependencies -------------------------------------------------

// `Show (Box a)` depends on `Show a`, but takes that dictionary as a PARAMETER
// (a given) — it does not bake in any concrete element instance. So editing a
// concrete element instance must not re-codegen `Show (Box a)`, and vice-versa.
const INSTDEP_V1: &str = "\
module M where

class Show a where
  show :: a -> String

data Color = Red | Green

instance Show Color where
  show Red = \"Red\"
  show Green = \"Green\"

data Box a = Box a

instance Show a => Show (Box a) where
  show (Box x) = show x
";

#[test]
fn instdep_noop_rebuild_all_hit() {
    let mut db = new_db();
    run(&mut db, &[("M", INSTDEP_V1)]);
    let second = run(&mut db, &[("M", INSTDEP_V1)]);
    let outs = instance_outcomes(&second, "M");
    assert_eq!(outs.len(), 2);
    assert_eq!(count_miss(&outs), 0, "unchanged instances all hit");
}

#[test]
fn instdep_edit_element_instance_leaves_container_cached() {
    // Edit the concrete `Show Color` body. `Show (Box a)` resolves its element
    // dict from a parameter, so its codegen is independent → only Show Color
    // re-codegens.
    let v2 = INSTDEP_V1.replace("show Green = \"Green\"", "show Green = \"GREEN\"");
    let mut db = new_db();
    run(&mut db, &[("M", INSTDEP_V1)]);
    let second = run(&mut db, &[("M", &v2)]);
    assert_eq!(
        count_miss(&instance_outcomes(&second, "M")),
        1,
        "only the edited element instance (Show Color) rebuilds; Show (Box a) is independent"
    );
}

#[test]
fn instdep_edit_container_instance_leaves_element_cached() {
    let v2 = INSTDEP_V1.replace("show (Box x) = show x", "show (Box y) = show y");
    let mut db = new_db();
    run(&mut db, &[("M", INSTDEP_V1)]);
    let second = run(&mut db, &[("M", &v2)]);
    assert_eq!(
        count_miss(&instance_outcomes(&second, "M")),
        1,
        "only Show (Box a) rebuilds; Show Color is untouched"
    );
}

#[test]
fn instdep_adding_unrelated_instance_leaves_existing_cached() {
    // A brand-new instance for a brand-new type cannot change how the existing
    // instances' method bodies resolve, so they must stay cached.
    let v2 = format!(
        "{INSTDEP_V1}\ndata Other = Other\n\ninstance Show Other where\n  show Other = \"Other\"\n"
    );
    let mut db = new_db();
    run(&mut db, &[("M", INSTDEP_V1)]);
    let second = run(&mut db, &[("M", &v2)]);
    let outs = instance_outcomes(&second, "M");
    assert_eq!(outs.len(), 3, "three instances now");
    assert_eq!(
        count_miss(&outs),
        1,
        "only the newly-added instance is fresh; the two existing instances stay cached"
    );
}

// --- multi-parameter type classes ------------------------------------------

const MULTIPARAM_V1: &str = "\
module M where

class Convert a b where
  convert :: a -> b

data A = A
data B = B

instance Convert A B where
  convert _ = B

instance Convert B A where
  convert _ = A
";

#[test]
fn multiparam_noop_rebuild_all_hit() {
    let mut db = new_db();
    run(&mut db, &[("M", MULTIPARAM_V1)]);
    let second = run(&mut db, &[("M", MULTIPARAM_V1)]);
    let outs = instance_outcomes(&second, "M");
    assert_eq!(outs.len(), 2);
    assert_eq!(count_miss(&outs), 0);
}

#[test]
fn multiparam_edit_one_instance_leaves_sibling_cached() {
    // Real body edit (rename the binder) to the `Convert A B` instance.
    let v2 = MULTIPARAM_V1.replace("instance Convert A B where\n  convert _ = B", "instance Convert A B where\n  convert _x = B");
    let mut db = new_db();
    run(&mut db, &[("M", MULTIPARAM_V1)]);
    let second = run(&mut db, &[("M", &v2)]);
    assert_eq!(
        count_miss(&instance_outcomes(&second, "M")),
        1,
        "editing Convert A B must not rebuild Convert B A"
    );
}

#[test]
fn multiparam_edit_class_rebuilds_all_its_instances() {
    // Changing the class (here: add a second method) changes the dict shape, so
    // every instance of it must re-codegen.
    let v2 = MULTIPARAM_V1
        .replace("  convert :: a -> b\n", "  convert :: a -> b\n  back :: b -> a\n")
        .replace("  convert _ = B\n", "  convert _ = B\n  back _ = A\n")
        .replace("  convert _ = A\n", "  convert _ = A\n  back _ = B\n");
    let mut db = new_db();
    run(&mut db, &[("M", MULTIPARAM_V1)]);
    let second = run(&mut db, &[("M", &v2)]);
    assert_eq!(
        count_miss(&instance_outcomes(&second, "M")),
        2,
        "a class-shape change rebuilds all its instances"
    );
    assert_eq!(
        outcome(&second, "M", "class__Convert"),
        CacheOutcome::Miss,
        "the class accessor decl rebuilds too"
    );
}

// --- superclasses ----------------------------------------------------------

const SUPERCLASS_V1: &str = "\
module M where

class Eq a where
  eq :: a -> a -> Boolean

class Eq a <= Ord a where
  cmp :: a -> a -> Int

data D = D

instance Eq D where
  eq _ _ = true

instance Ord D where
  cmp _ _ = 0
";

#[test]
fn superclass_noop_rebuild_all_hit() {
    let mut db = new_db();
    run(&mut db, &[("M", SUPERCLASS_V1)]);
    let second = run(&mut db, &[("M", SUPERCLASS_V1)]);
    let outs = instance_outcomes(&second, "M");
    assert_eq!(outs.len(), 2);
    assert_eq!(count_miss(&outs), 0);
}

#[test]
fn superclass_edit_superclass_instance_leaves_subclass_cached() {
    // The `Ord D` dict carries a superclass accessor `Eq0: () => eqD` that
    // references the Eq instance BY NAME. Editing `Eq D`'s body changes eqD's
    // definition but not its name, so `Ord D` stays byte-identical → cached.
    let v2 = SUPERCLASS_V1.replace("eq _ _ = true", "eq _ _ = false");
    let mut db = new_db();
    run(&mut db, &[("M", SUPERCLASS_V1)]);
    let second = run(&mut db, &[("M", &v2)]);
    assert_eq!(
        count_miss(&instance_outcomes(&second, "M")),
        1,
        "editing the Eq (superclass) instance must not rebuild the Ord (subclass) instance"
    );
}

#[test]
fn superclass_edit_subclass_instance_leaves_superclass_cached() {
    let v2 = SUPERCLASS_V1.replace("cmp _ _ = 0", "cmp _ _ = 1");
    let mut db = new_db();
    run(&mut db, &[("M", SUPERCLASS_V1)]);
    let second = run(&mut db, &[("M", &v2)]);
    assert_eq!(
        count_miss(&instance_outcomes(&second, "M")),
        1,
        "editing the Ord (subclass) instance must not rebuild the Eq (superclass) instance"
    );
}

#[test]
fn superclass_removing_superclass_relation_rebuilds_subclass_instance() {
    // Dropping `Eq a <=` removes the `Eq0` superclass accessor from every Ord
    // dict, so `Ord D`'s codegen changes and must rebuild. `Eq D` is unaffected.
    let v2 = SUPERCLASS_V1.replace("class Eq a <= Ord a where", "class Ord a where");
    let mut db = new_db();
    run(&mut db, &[("M", SUPERCLASS_V1)]);
    let second = run(&mut db, &[("M", &v2)]);
    let outs = instance_outcomes(&second, "M");
    assert_eq!(outs.len(), 2);
    assert_eq!(
        count_miss(&outs),
        1,
        "only the Ord instance (whose superclass accessor disappeared) rebuilds"
    );
}

// ---------------------------------------------------------------------------
// Baseline per-decl caching
// ---------------------------------------------------------------------------

#[test]
fn noop_rebuild_all_value_decls_hit() {
    let src = "\
module M where

foo :: Int
foo = 1

bar :: Int
bar = 2
";
    let mut db = new_db();
    let first = run(&mut db, &[("M", src)]);
    assert_eq!(outcome(&first, "M", "value__foo"), CacheOutcome::Miss);
    assert_eq!(outcome(&first, "M", "value__bar"), CacheOutcome::Miss);

    let second = run(&mut db, &[("M", src)]);
    assert_eq!(outcome(&second, "M", "value__foo"), CacheOutcome::Hit);
    assert_eq!(outcome(&second, "M", "value__bar"), CacheOutcome::Hit);
}

#[test]
fn body_edit_invalidates_only_that_value() {
    let v1 = "\
module M where

foo :: Int
foo = 1

bar :: Int
bar = 2
";
    let v2 = "\
module M where

foo :: Int
foo = 1

bar :: Int
bar = 99
";
    let mut db = new_db();
    run(&mut db, &[("M", v1)]);
    let second = run(&mut db, &[("M", v2)]);
    assert_eq!(
        outcome(&second, "M", "value__bar"),
        CacheOutcome::Miss,
        "edited bar must re-codegen"
    );
    assert_eq!(
        outcome(&second, "M", "value__foo"),
        CacheOutcome::Hit,
        "untouched foo must stay cached"
    );
}

#[test]
fn referencing_value_stays_cached_when_callees_body_edited() {
    // `user` calls `helper`. Editing `helper`'s body (scheme unchanged) must
    // NOT re-codegen `user` — `user` only references `helper` by name.
    let v1 = "\
module M where

helper :: Int -> Int
helper x = x

user :: Int
user = helper 1
";
    let v2 = "\
module M where

helper :: Int -> Int
helper x = x + 0

user :: Int
user = helper 1
";
    let mut db = new_db();
    run(&mut db, &[("M", v1)]);
    let second = run(&mut db, &[("M", v2)]);
    assert_eq!(
        outcome(&second, "M", "value__helper"),
        CacheOutcome::Miss,
        "helper's body changed"
    );
    assert_eq!(
        outcome(&second, "M", "value__user"),
        CacheOutcome::Hit,
        "user only references helper by name; its JS is unchanged"
    );
}

#[test]
fn editing_a_later_equation_of_a_multi_equation_value_invalidates_it() {
    // Multi-equation decls are merged into a single IR decl whose span covers
    // only the FIRST equation; the source hash must still cover later equations.
    let v1 = "\
module M where

f :: Int -> String
f 0 = \"zero\"
f _ = \"other\"

g :: Int
g = 1
";
    let v2 = "\
module M where

f :: Int -> String
f 0 = \"zero\"
f _ = \"OTHER\"

g :: Int
g = 1
";
    let mut db = new_db();
    run(&mut db, &[("M", v1)]);
    let second = run(&mut db, &[("M", v2)]);
    assert_eq!(
        outcome(&second, "M", "value__f"),
        CacheOutcome::Miss,
        "editing f's second equation must re-codegen f"
    );
    assert_eq!(outcome(&second, "M", "value__g"), CacheOutcome::Hit);
}

#[test]
fn adding_a_decl_leaves_existing_decls_cached() {
    let v1 = "\
module M where

foo :: Int
foo = 1

bar :: Int
bar = 2
";
    let v2 = "\
module M where

foo :: Int
foo = 1

bar :: Int
bar = 2

baz :: Int
baz = 3
";
    let mut db = new_db();
    run(&mut db, &[("M", v1)]);
    let second = run(&mut db, &[("M", v2)]);
    assert_eq!(outcome(&second, "M", "value__foo"), CacheOutcome::Hit);
    assert_eq!(outcome(&second, "M", "value__bar"), CacheOutcome::Hit);
    assert_eq!(outcome(&second, "M", "value__baz"), CacheOutcome::Miss);
    assert_eq!(
        outcome(&second, "M", "$module"),
        CacheOutcome::Miss,
        "the new decl changes the assembled unit set"
    );
}

#[test]
fn polymorphic_class_method_user_caches_across_runs() {
    // `useM` is constrained (`C a => a -> Int`); its dict comes in as a
    // parameter (a given), exercising the constraint-dict codegen path. A no-op
    // rebuild must cache it.
    let src = "\
module M where

class C a where
  m :: a -> Int

useM :: forall a. C a => a -> Int
useM x = m x
";
    let mut db = new_db();
    run(&mut db, &[("M", src)]);
    let second = run(&mut db, &[("M", src)]);
    assert_eq!(outcome(&second, "M", "value__useM"), CacheOutcome::Hit);
    assert_eq!(outcome(&second, "M", "$module"), CacheOutcome::Hit);
}

// ---------------------------------------------------------------------------
// Module assembly caching
// ---------------------------------------------------------------------------

#[test]
fn noop_rebuild_module_assembly_hits() {
    let src = "\
module M where

foo :: Int
foo = 1
";
    let mut db = new_db();
    let first = run(&mut db, &[("M", src)]);
    assert_eq!(outcome(&first, "M", "$module"), CacheOutcome::Miss);

    let second = run(&mut db, &[("M", src)]);
    assert_eq!(
        outcome(&second, "M", "$module"),
        CacheOutcome::Hit,
        "an unchanged module must not be reassembled"
    );
}

#[test]
fn any_decl_edit_reassembles_module() {
    let v1 = "\
module M where

foo :: Int
foo = 1

bar :: Int
bar = 2
";
    let v2 = "\
module M where

foo :: Int
foo = 1

bar :: Int
bar = 3
";
    let mut db = new_db();
    run(&mut db, &[("M", v1)]);
    let second = run(&mut db, &[("M", v2)]);
    assert_eq!(
        outcome(&second, "M", "$module"),
        CacheOutcome::Miss,
        "a changed decl's output must reassemble the module"
    );
    assert_eq!(outcome(&second, "M", "value__foo"), CacheOutcome::Hit);
    assert_eq!(outcome(&second, "M", "value__bar"), CacheOutcome::Miss);
}

// ---------------------------------------------------------------------------
// Derive caching
// ---------------------------------------------------------------------------

const DERIVE_V1: &str = "\
module M where

class Eq a where
  eq :: a -> a -> Boolean

data T = A | B

derive instance Eq T
";

#[test]
fn noop_rebuild_derive_hits() {
    let mut db = new_db();
    let first = run(&mut db, &[("M", DERIVE_V1)]);
    assert_eq!(count_miss(&instance_outcomes(&first, "M")), 1, "fresh derive");

    let second = run(&mut db, &[("M", DERIVE_V1)]);
    assert_eq!(
        count_miss(&instance_outcomes(&second, "M")),
        0,
        "unchanged derive must cache-hit"
    );
}

#[test]
fn derive_subject_data_edit_recodegens_derive() {
    // Adding a constructor to the derived-over data type changes the derived
    // `eq`'s structure, so the derive must re-codegen.
    let v2 = "\
module M where

import Data.Eq (class Eq)

data T = A | B | Cc

derive instance Eq T
";
    let mut db = new_db();
    run(&mut db, &[("M", DERIVE_V1)]);
    let second = run(&mut db, &[("M", v2)]);
    assert_eq!(
        count_miss(&instance_outcomes(&second, "M")),
        1,
        "editing the derived-over data type must re-codegen its derive"
    );
}

// ---------------------------------------------------------------------------
// Cross-module precision
// ---------------------------------------------------------------------------

#[test]
fn cross_module_instance_body_edit_leaves_user_module_fully_cached() {
    // A defines a class + instance; B calls the method. Editing A's instance
    // method body must re-codegen A's instance, but B references the dictionary
    // by name only — so every B decl AND B's assembly stay cached.
    let a_v1 = "\
module A where

class C a where
  m :: a -> Int

data X = X

instance C X where
  m _ = 1
";
    let a_v2 = "\
module A where

class C a where
  m :: a -> Int

data X = X

instance C X where
  m _ = 42
";
    let b = "\
module B where

import A

useC :: X -> Int
useC v = m v
";
    let mut db = new_db();
    run(&mut db, &[("A", a_v1), ("B", b)]);
    let second = run(&mut db, &[("A", a_v2), ("B", b)]);

    // A's instance regenerated; B untouched.
    assert_eq!(
        count_miss(&instance_outcomes(&second, "A")),
        1,
        "A's edited instance must re-codegen"
    );
    assert_eq!(
        outcome(&second, "B", "value__useC"),
        CacheOutcome::Hit,
        "B references A's dict by name; its codegen is unchanged"
    );
    assert_eq!(
        outcome(&second, "B", "$module"),
        CacheOutcome::Hit,
        "B's assembly must stay cached when only A's instance body changed"
    );
}

#[test]
fn data_to_newtype_toggle_recodegens_constructor_user() {
    // `data T = T Int` emits `T.create(x)`; `newtype T = T Int` erases to
    // identity. The ctor `T`'s scheme (`Int -> T`) is identical across the
    // toggle, so `mk`'s inferred type/dicts don't change — only its generated
    // JS does. The ctor-ABI dependency is what forces the re-codegen.
    let as_data = "\
module M where

data T = T Int

mk :: T
mk = T 1
";
    let as_newtype = "\
module M where

newtype T = T Int

mk :: T
mk = T 1
";
    let mut db = new_db();
    run(&mut db, &[("M", as_data)]);
    let second = run(&mut db, &[("M", as_newtype)]);
    assert_eq!(
        outcome(&second, "M", "value__mk"),
        CacheOutcome::Miss,
        "mk constructs T, whose ABI changed (data->newtype); its JS must regenerate"
    );
}

// ---------------------------------------------------------------------------
// Instance caching
// ---------------------------------------------------------------------------

const TWO_INSTANCES_V1: &str = "\
module M where

class C a where
  m :: a -> Int

data X = X
data Y = Y

instance C X where
  m _ = 1

instance C Y where
  m _ = 2
";

#[test]
fn noop_rebuild_instances_hit() {
    let mut db = new_db();
    let first = run(&mut db, &[("M", TWO_INSTANCES_V1)]);
    assert_eq!(count_miss(&instance_outcomes(&first, "M")), 2, "both fresh");

    let second = run(&mut db, &[("M", TWO_INSTANCES_V1)]);
    let outs = instance_outcomes(&second, "M");
    assert_eq!(outs.len(), 2, "two instances present");
    assert_eq!(count_miss(&outs), 0, "unchanged instances must all cache-hit");
}

#[test]
fn instance_body_edit_invalidates_only_that_instance() {
    let v2 = "\
module M where

class C a where
  m :: a -> Int

data X = X
data Y = Y

instance C X where
  m _ = 1

instance C Y where
  m _ = 999
";
    let mut db = new_db();
    run(&mut db, &[("M", TWO_INSTANCES_V1)]);
    let second = run(&mut db, &[("M", v2)]);
    let outs = instance_outcomes(&second, "M");
    assert_eq!(outs.len(), 2);
    assert_eq!(
        count_miss(&outs),
        1,
        "editing one instance's method body must re-codegen exactly that instance"
    );
}

#[test]
fn editing_one_module_leaves_other_module_cached() {
    let a = "\
module A where

ax :: Int
ax = 1
";
    let b1 = "\
module B where

bx :: Int
bx = 10
";
    let b2 = "\
module B where

bx :: Int
bx = 20
";
    let mut db = new_db();
    run_named(&mut db, &[a, b1]);
    let second = run_named(&mut db, &[a, b2]);
    assert_eq!(outcome(&second, "A", "value__ax"), CacheOutcome::Hit);
    assert_eq!(outcome(&second, "B", "value__bx"), CacheOutcome::Miss);
}
