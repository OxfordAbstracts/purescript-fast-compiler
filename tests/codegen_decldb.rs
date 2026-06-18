//! Runtime tests for the NEW per-declaration codegen driven by typecheck_db
//! (the `DeclDb` engine), as opposed to the legacy whole-module codegen in
//! `tests/codegen.rs`.
//!
//! Each fixture is a self-contained PureScript module that exports a top-level
//! `test` binding and carries a `-- TEST: <expected>` comment. We:
//!   1. typecheck it through `check_many_modules_with_db` with codegen enabled,
//!   2. write the generated `js_module_text` to a temp dir as an ES module,
//!   3. run it under Node, `JSON.stringify`-ing the exported `test`,
//!   4. assert the printed value equals the expected string.

use purescript_fast_compiler::parse;
use purescript_fast_compiler::typecheck_db::driver_multi::{
    check_many_modules_with_db, ModuleInput,
};
use purescript_fast_compiler::typecheck_db::TypecheckDb;
use std::collections::HashMap;
use std::path::PathBuf;
use std::process::Command;

/// Extract the first `-- TEST:` expectation from the source.
fn extract_expected(source: &str) -> Option<String> {
    source.lines().find_map(|l| {
        let t = l.trim();
        t.strip_prefix("-- TEST:").map(|rest| rest.trim().to_string())
    })
}

/// Extract `module X.Y where` → "X.Y".
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

/// Generate JS for a single self-contained module via the DeclDb engine.
fn gen_decldb(source: &str) -> (String, String) {
    let module_name = extract_module_name(source);
    let cst = parse(source).expect("parse failed");
    let input = ModuleInput::new(module_name.clone(), source.to_string(), cst);

    let mut db = TypecheckDb::open_in_memory().expect("in-memory db");
    db.set_codegen(true);
    let report = check_many_modules_with_db(&mut db, vec![input]);

    assert!(
        report.errors.is_empty(),
        "multi-module errors: {:?}",
        report.errors
    );
    let result = report
        .results
        .into_iter()
        .find(|r| r.name == module_name)
        .expect("module result");
    assert!(
        result.inference_error.is_none(),
        "inference error: {:?}",
        result.inference_error
    );
    assert!(
        result.constraint_errors.is_empty(),
        "constraint errors: {:?}",
        result.constraint_errors
    );
    let js = result
        .js_module_text
        .expect("codegen produced no js_module_text");
    (module_name, js)
}

/// Build the module + a run.mjs to a temp dir and run it under Node, returning
/// the trimmed stdout. `ffi` is the optional FFI companion module source.
fn run_under_node(test_name: &str, module_name: &str, js: &str, ffi: Option<&str>) -> String {
    let out_dir = std::env::temp_dir().join(format!("pfc-decldb-{test_name}"));
    let _ = std::fs::remove_dir_all(&out_dir);
    let module_dir = out_dir.join(module_name);
    std::fs::create_dir_all(&module_dir).expect("create module dir");
    std::fs::write(module_dir.join("index.js"), js).expect("write index.js");
    if let Some(ffi_src) = ffi {
        std::fs::write(module_dir.join("foreign.js"), ffi_src).expect("write foreign.js");
    }

    let run = format!(
        "import {{ test }} from './{module_name}/index.js';\n\
         process.stdout.write(JSON.stringify(test));\n"
    );
    let run_path = out_dir.join("run.mjs");
    std::fs::write(&run_path, run).expect("write run.mjs");

    let output = Command::new("node")
        .arg("run.mjs")
        .current_dir(&out_dir)
        .output()
        .expect("run node");
    assert!(
        output.status.success(),
        "node failed.\n--- stdout ---\n{}\n--- stderr ---\n{}\n--- js ---\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
        js,
    );
    String::from_utf8_lossy(&output.stdout).trim().to_string()
}

fn run_fixture(test_name: &str, source: &str) {
    run_fixture_ffi(test_name, source, None);
}

fn run_fixture_ffi(test_name: &str, source: &str, ffi: Option<&str>) {
    let expected = extract_expected(source)
        .unwrap_or_else(|| panic!("fixture {test_name} has no -- TEST: line"));
    let (module_name, js) = gen_decldb(source);
    let got = run_under_node(test_name, &module_name, &js, ffi);
    assert_eq!(got, expected, "\n--- generated js ---\n{js}");
}

/// Generate JS for several modules at once via the DeclDb engine, returning
/// (module_name, js) for each.
fn gen_decldb_multi(modules: &[&str]) -> Vec<(String, String)> {
    let inputs: Vec<ModuleInput> = modules
        .iter()
        .map(|src| {
            let name = extract_module_name(src);
            let cst = parse(src).expect("parse failed");
            ModuleInput::new(name, src.to_string(), cst)
        })
        .collect();

    let mut db = TypecheckDb::open_in_memory().expect("in-memory db");
    db.set_codegen(true);
    let report = check_many_modules_with_db(&mut db, inputs);
    assert!(report.errors.is_empty(), "multi-module errors: {:?}", report.errors);
    for r in &report.results {
        assert!(
            r.inference_error.is_none() && r.constraint_errors.is_empty(),
            "module {} errors: inference={:?} constraints={:?}",
            r.name, r.inference_error, r.constraint_errors
        );
    }
    report
        .results
        .into_iter()
        .map(|r| (r.name.clone(), r.js_module_text.expect("js_module_text")))
        .collect()
}

/// Build a multi-module program to a temp dir and run the `test` export of
/// `entry_module` under Node, asserting against `expected`.
fn run_multi(test_name: &str, modules: &[&str], entry_module: &str, expected: &str) {
    let outputs = gen_decldb_multi(modules);
    let out_dir = std::env::temp_dir().join(format!("pfc-decldb-{test_name}"));
    let _ = std::fs::remove_dir_all(&out_dir);
    for (name, js) in &outputs {
        let dir = out_dir.join(name);
        std::fs::create_dir_all(&dir).expect("module dir");
        std::fs::write(dir.join("index.js"), js).expect("index.js");
    }
    let run = format!(
        "import {{ test }} from './{entry_module}/index.js';\n\
         process.stdout.write(JSON.stringify(test));\n"
    );
    std::fs::write(out_dir.join("run.mjs"), run).expect("run.mjs");
    let output = Command::new("node")
        .arg("run.mjs")
        .current_dir(&out_dir)
        .output()
        .expect("run node");
    assert!(
        output.status.success(),
        "node failed.\n--- stderr ---\n{}\n--- {entry_module} js ---\n{}",
        String::from_utf8_lossy(&output.stderr),
        outputs.iter().find(|(n, _)| n == entry_module).map(|(_, j)| j.as_str()).unwrap_or(""),
    );
    assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), expected);
}

#[allow(dead_code)]
fn fixture_path(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/codegen_decldb")
        .join(name)
}

// ---------------------------------------------------------------------------
// Self-hosted Prelude harness: build EVERY module (support packages + the test
// module) with our own DeclDb codegen, write them all to disk with their FFI
// companions, and run under Node.
// ---------------------------------------------------------------------------

fn collect_purs(dir: &std::path::Path, out: &mut Vec<PathBuf>) {
    if let Ok(entries) = std::fs::read_dir(dir) {
        for e in entries.flatten() {
            let p = e.path();
            if p.is_dir() {
                collect_purs(&p, out);
            } else if p.extension().is_some_and(|x| x == "purs") {
                out.push(p);
            }
        }
    }
}

/// Load (source, optional-ffi) for every `.purs` in the given support packages.
fn load_support(packages: &[&str]) -> Vec<(String, Option<String>)> {
    let base = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/packages");
    let mut out = Vec::new();
    for pkg in packages {
        let mut files = Vec::new();
        collect_purs(&base.join(pkg).join("src"), &mut files);
        for f in files {
            if let Ok(src) = std::fs::read_to_string(&f) {
                let ffi = std::fs::read_to_string(f.with_extension("js")).ok();
                out.push((src, ffi));
            }
        }
    }
    out
}

/// Build the whole program (support packages + test module) with DeclDb codegen,
/// write all modules + FFI to a temp dir, run `test` from `Test` under Node.
fn run_prelude(test_name: &str, packages: &[&str], test_source: &str, expected: &str) {
    let mut units: Vec<(String, Option<String>)> = load_support(packages);
    units.push((test_source.to_string(), None));

    // Typecheck + codegen everything via DeclDb.
    let mut inputs = Vec::new();
    for (src, _) in &units {
        let name = extract_module_name(src);
        let cst = parse(src).unwrap_or_else(|e| panic!("parse {name}: {e:?}"));
        inputs.push(ModuleInput::new(name, src.clone(), cst));
    }
    let mut db = TypecheckDb::open_in_memory().expect("db");
    db.set_codegen(true);
    let report = check_many_modules_with_db(&mut db, inputs);
    assert!(report.errors.is_empty(), "module graph errors: {:?}", report.errors);
    // Only the test module must be error-free; support modules may have
    // pre-existing type errors that don't affect the runtime path under test.
    if let Some(t) = report.results.iter().find(|r| r.name == "Test") {
        assert!(
            t.inference_error.is_none() && t.constraint_errors.is_empty(),
            "Test errors: inference={:?} constraints={:?}",
            t.inference_error, t.constraint_errors
        );
    }

    // FFI by module name (from the sibling .js of each support source).
    let mut ffi_by_module: HashMap<String, String> = HashMap::new();
    for (src, ffi) in &units {
        if let Some(js) = ffi {
            ffi_by_module.insert(extract_module_name(src), js.clone());
        }
    }

    let out_dir = std::env::temp_dir().join(format!("pfc-decldb-prelude-{test_name}"));
    let _ = std::fs::remove_dir_all(&out_dir);
    for r in &report.results {
        let Some(js) = &r.js_module_text else { continue };
        let dir = out_dir.join(&r.name);
        std::fs::create_dir_all(&dir).expect("module dir");
        std::fs::write(dir.join("index.js"), js).expect("index.js");
        if let Some(ffi) = ffi_by_module.get(&r.name) {
            std::fs::write(dir.join("foreign.js"), ffi).expect("foreign.js");
        }
    }

    let run = "import { test } from './Test/index.js';\n\
               process.stdout.write(JSON.stringify(test));\n";
    std::fs::write(out_dir.join("run.mjs"), run).expect("run.mjs");
    let output = Command::new("node")
        .arg("run.mjs")
        .current_dir(&out_dir)
        .output()
        .expect("node");
    assert!(
        output.status.success(),
        "node failed.\n--- stderr ---\n{}\n--- Test/index.js ---\n{}",
        String::from_utf8_lossy(&output.stderr),
        report.results.iter().find(|r| r.name == "Test").and_then(|r| r.js_module_text.as_deref()).unwrap_or(""),
    );
    assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), expected);
}

#[test]
fn codegen_prelude_arithmetic() {
    let source = r#"
module Test where

import Prelude

test :: Int
test = 1 + 2 * 3
-- TEST: 7
"#;
    run_prelude("arithmetic", &["prelude"], source, "7");
}

#[test]
fn codegen_prelude_show_int() {
    let source = r#"
module Test where

import Prelude

test :: String
test = show 42
-- TEST: "42"
"#;
    run_prelude("show_int", &["prelude"], source, "\"42\"");
}

#[test]
fn codegen_prelude_eq() {
    let source = r#"
module Test where

import Prelude

test :: Boolean
test = (1 == 2)
-- TEST: false
"#;
    run_prelude("eq", &["prelude"], source, "false");
}

#[test]
fn codegen_prelude_string_append() {
    let source = r#"
module Test where

import Prelude

test :: String
test = "ab" <> "cd"
-- TEST: "abcd"
"#;
    run_prelude("string_append", &["prelude"], source, "\"abcd\"");
}

#[test]
fn codegen_prelude_do_maybe() {
    let source = r#"
module Test where

import Prelude
import Data.Maybe (Maybe(..), fromMaybe)

addM :: Maybe Int
addM = do
  x <- Just 40
  y <- Just 2
  pure (x + y)

test :: Int
test = fromMaybe 0 addM
-- TEST: 42
"#;
    run_prelude("do_maybe", &["prelude", "maybe", "control", "invariant"], source, "42");
}

#[test]
fn codegen_prelude_ado_maybe() {
    let source = r#"
module Test where

import Prelude
import Data.Maybe (Maybe(..), fromMaybe)

sumA :: Maybe Int
sumA = ado
  x <- Just 40
  y <- Just 2
  in x + y

test :: Int
test = fromMaybe 0 sumA
-- TEST: 42
"#;
    run_prelude("ado_maybe", &["prelude", "maybe", "control", "invariant"], source, "42");
}

#[test]
fn codegen_prelude_do_short_circuit() {
    // `Nothing` short-circuits the bind chain.
    let source = r#"
module Test where

import Prelude
import Data.Maybe (Maybe(..), fromMaybe)

chain :: Maybe Int
chain = do
  x <- Just 1
  _ <- Nothing
  pure x

test :: Int
test = fromMaybe 99 chain
-- TEST: 99
"#;
    run_prelude("do_short_circuit", &["prelude", "maybe", "control", "invariant"], source, "99");
}

#[test]
fn codegen_prelude_derive_eq() {
    let source = r#"
module Test where

import Prelude

data RGB = Red | Green | Blue
derive instance Eq RGB

test :: Boolean
test = (Green == Green) && (Red == Blue)
-- TEST: false
"#;
    run_prelude("derive_eq", &["prelude"], source, "false");
}

#[test]
fn codegen_prelude_derive_eq_fields() {
    let source = r#"
module Test where

import Prelude

data Point = Point Int Int
derive instance Eq Point

test :: Boolean
test = (Point 1 2 == Point 1 2) && (Point 1 2 == Point 1 3)
-- TEST: false
"#;
    run_prelude("derive_eq_fields", &["prelude"], source, "false");
}

#[test]
fn codegen_prelude_derive_functor() {
    let source = r#"
module Test where

import Prelude

data Box a = Box a
derive instance Functor Box

unBox :: Box Int -> Int
unBox (Box n) = n

test :: Int
test = unBox (map (\x -> x + 1) (Box 41))
-- TEST: 42
"#;
    run_prelude("derive_functor", &["prelude"], source, "42");
}

#[test]
fn codegen_prelude_derive_functor_nested() {
    let source = r#"
module Test where

import Prelude
import Data.Maybe (Maybe(..), fromMaybe)

data Wrap a = Wrap (Maybe a)
derive instance Functor Wrap

unwrap :: Wrap Int -> Int
unwrap (Wrap m) = fromMaybe 0 m

test :: Int
test = unwrap (map (\x -> x + 1) (Wrap (Just 41)))
-- TEST: 42
"#;
    run_prelude("derive_functor_nested", &["prelude", "maybe", "control", "invariant"], source, "42");
}

#[test]
fn codegen_prelude_derive_foldable() {
    let source = r#"
module Test where

import Prelude
import Data.Foldable (foldr, foldl)

data Pair a = Pair a a
derive instance Foldable Pair

test :: Int
test = foldr (\x acc -> x + acc) 0 (Pair 40 2) + foldl (\acc x -> acc + x) 0 (Pair 30 0)
-- TEST: 72
"#;
    run_prelude(
        "derive_foldable",
        &["prelude", "foldable-traversable", "maybe", "control", "invariant", "newtype", "tuples", "either", "const", "identity", "functors", "safe-coerce", "unsafe-coerce"],
        source,
        "72",
    );
}

#[test]
fn codegen_prelude_derive_foldable_foldmap() {
    let source = r#"
module Test where

import Prelude
import Data.Foldable (foldMap)

data Pair a = Pair a a
derive instance Foldable Pair

test :: String
test = foldMap (\x -> x) (Pair "ab" "cd")
-- TEST: "abcd"
"#;
    run_prelude(
        "derive_foldmap",
        &["prelude", "foldable-traversable", "maybe", "control", "invariant", "newtype", "tuples", "either", "const", "identity", "functors", "safe-coerce", "unsafe-coerce"],
        source,
        "\"abcd\"",
    );
}

#[test]
fn codegen_prelude_derive_traversable() {
    let source = r#"
module Test where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse)

data Pair a = Pair a a
derive instance Functor Pair
derive instance Foldable Pair
derive instance Traversable Pair

test :: Int
test = case traverse (\x -> Just x) (Pair 40 2) of
  Just (Pair a b) -> a + b
  Nothing -> 0
-- TEST: 42
"#;
    run_prelude(
        "derive_traversable",
        &["prelude", "foldable-traversable", "maybe", "control", "invariant", "newtype", "tuples", "either", "const", "identity", "functors", "safe-coerce", "unsafe-coerce"],
        source,
        "42",
    );
}

#[test]
fn codegen_prelude_derive_eq1() {
    let source = r#"
module Test where

import Prelude
import Data.Eq (class Eq1, eq1)

data Box a = Box a
derive instance Eq1 Box

test :: Boolean
test = eq1 (Box 1) (Box 1) && (eq1 (Box 1) (Box 2) == false)
-- TEST: true
"#;
    run_prelude("derive_eq1", &["prelude"], source, "true");
}

#[test]
fn codegen_prelude_derive_ord1() {
    let source = r#"
module Test where

import Prelude
import Data.Eq (class Eq1)
import Data.Ord (class Ord1, compare1)

data Box a = Box a
derive instance Eq1 Box
derive instance Ord1 Box

test :: Boolean
test = compare1 (Box 1) (Box 2) == LT
-- TEST: true
"#;
    run_prelude("derive_ord1", &["prelude"], source, "true");
}

#[test]
fn codegen_prelude_derive_ord() {
    let source = r#"
module Test where

import Prelude

data RGB = Red | Green | Blue
derive instance Eq RGB
derive instance Ord RGB

test :: Boolean
test = (compare Red Blue == LT) && (compare Blue Red == GT)
-- TEST: true
"#;
    run_prelude("derive_ord", &["prelude"], source, "true");
}

#[test]
fn codegen_prelude_eqord_compare() {
    let source = r#"
module Test where

import Prelude

test :: Boolean
test = compare 2 1 == GT
-- TEST: true
"#;
    run_prelude("compare", &["prelude"], source, "true");
}

// ---------------------------------------------------------------------------
// Production build API (build_from_sources_decldb)
// ---------------------------------------------------------------------------

#[test]
fn build_api_decldb_cross_module() {
    use purescript_fast_compiler::build::build_from_sources_decldb;
    let lib = "module Lib where\n\nanswer :: Int\nanswer = 42\n";
    let main = "module Main where\nimport Lib\ntest :: Int\ntest = answer\n";
    let sources = [("Lib.purs", lib), ("Main.purs", main)];
    let out = std::env::temp_dir().join("pfc-decldb-buildapi");
    let _ = std::fs::remove_dir_all(&out);

    let result = build_from_sources_decldb(&sources, &None, Some(&out), None);
    assert!(result.graph_errors.is_empty(), "graph errors: {:?}", result.graph_errors);
    assert!(result.parse_errors.is_empty(), "parse errors: {:?}", result.parse_errors);
    assert!(result.modules.iter().all(|m| m.error_count == 0), "type errors present");
    assert!(result.modules.iter().any(|m| m.name == "Main" && m.wrote_js));

    let run = "import { test } from './Main/index.js';\n\
               process.stdout.write(JSON.stringify(test));\n";
    std::fs::write(out.join("run.mjs"), run).unwrap();
    let output = Command::new("node").arg("run.mjs").current_dir(&out).output().unwrap();
    assert!(output.status.success(), "node: {}", String::from_utf8_lossy(&output.stderr));
    assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "42");
}

// ---------------------------------------------------------------------------
// Phase 5b: cross-module references (values, constructors, class instances)
// ---------------------------------------------------------------------------

#[test]
fn codegen_p5_cross_module_value() {
    let lib = r#"
module Lib where

double :: Int -> Int
double = \x -> x

answer :: Int
answer = 42
"#;
    let main = r#"
module Main where

import Lib

test :: Int
test = answer
"#;
    run_multi("p5_xmod_value", &[lib, main], "Main", "42");
}

#[test]
fn codegen_p5_cross_module_instance() {
    // Class, data type, and instance all in Lib; Main dispatches the method on
    // a Lib constructor. Exercises imported class accessor + imported
    // constructor + imported instance dictionary (module accessors).
    let lib = r#"
module Lib where

class ToInt a where
  toInt :: a -> Int

data Color = Red | Green | Blue

instance ToInt Color where
  toInt Red = 0
  toInt Green = 1
  toInt Blue = 2
"#;
    let main = r#"
module Main where

import Lib

test :: Int
test = toInt Blue
"#;
    run_multi("p5_xmod_instance", &[lib, main], "Main", "2");
}

// ---------------------------------------------------------------------------
// Phase 1: primitives & simple expressions (no typeclasses, no dicts)
// ---------------------------------------------------------------------------

#[test]
fn codegen_p1_primitives() {
    let source = r#"
module Test where

identityNum :: Int -> Int
identityNum = \x -> x

pickFirst :: Int -> Int -> Int
pickFirst = \a -> \b -> a

rec :: { a :: Int, b :: Int }
rec = { a: 42, b: 20 }

test :: Int
test = if true then pickFirst (identityNum rec.a) rec.b else 0
-- TEST: 42
"#;
    run_fixture("p1_primitives", source);
}

#[test]
fn codegen_p1_literals() {
    let source = r#"
module Test where

test :: Array Int
test = [1, 2, 3]
-- TEST: [1,2,3]
"#;
    run_fixture("p1_literals", source);
}

#[test]
fn codegen_p1_string_record() {
    let source = r#"
module Test where

test :: { name :: String, ok :: Boolean }
test = { name: "hello", ok: true }
-- TEST: {"name":"hello","ok":true}
"#;
    run_fixture("p1_string_record", source);
}

// ---------------------------------------------------------------------------
// Phase 2: data types, constructors, newtypes. We JSON-stringify the
// constructed value directly, which verifies the runtime ABI (value0..,
// nullary singletons, newtype erasure) without needing pattern matching.
// ---------------------------------------------------------------------------

#[test]
fn codegen_p2_data_multifield() {
    let source = r#"
module Test where

data Pair = Pair Int Int

test :: Pair
test = Pair 42 7
-- TEST: {"value0":42,"value1":7}
"#;
    run_fixture("p2_data_multifield", source);
}

#[test]
fn codegen_p2_data_singlefield_curried() {
    // Constructor used partially applied then applied (curried `.create`).
    let source = r#"
module Test where

data Box = Box Int

mk :: Int -> Box
mk = Box

test :: Box
test = mk 42
-- TEST: {"value0":42}
"#;
    run_fixture("p2_data_singlefield", source);
}

#[test]
fn codegen_p2_nullary_ctor() {
    // Nullary constructor → empty singleton object.
    let source = r#"
module Test where

data Color = Red | Green | Blue

test :: Color
test = Green
-- TEST: {}
"#;
    run_fixture("p2_nullary_ctor", source);
}

#[test]
fn codegen_p2_newtype_identity() {
    // Newtype constructor is the identity function: `Wrapped 99` is just `99`.
    let source = r#"
module Test where

newtype Wrapped = Wrapped Int

test :: Wrapped
test = Wrapped 99
-- TEST: 99
"#;
    run_fixture("p2_newtype_identity", source);
}

// ---------------------------------------------------------------------------
// Phase 3: pattern matching, multi-equation, guards, let/where
// ---------------------------------------------------------------------------

#[test]
fn codegen_p3_case_constructor() {
    let source = r#"
module Test where

data Maybe a = Nothing | Just a

fromMaybe :: Int -> Maybe Int -> Int
fromMaybe d m = case m of
  Nothing -> d
  Just x -> x

test :: Int
test = fromMaybe 0 (Just 42)
-- TEST: 42
"#;
    run_fixture("p3_case_ctor", source);
}

#[test]
fn codegen_p3_case_nullary() {
    let source = r#"
module Test where

data Maybe a = Nothing | Just a

orZero :: Maybe Int -> Int
orZero m = case m of
  Nothing -> 0
  Just x -> x

test :: Int
test = orZero Nothing
-- TEST: 0
"#;
    run_fixture("p3_case_nullary", source);
}

#[test]
fn codegen_p3_multi_equation() {
    let source = r#"
module Test where

data Maybe a = Nothing | Just a

unMaybe :: Maybe Int -> Int
unMaybe Nothing = 100
unMaybe (Just x) = x

test :: Int
test = unMaybe (Just 42)
-- TEST: 42
"#;
    run_fixture("p3_multi_equation", source);
}

#[test]
fn codegen_p3_guards() {
    // Boolean guards with a `| true` fallback (no Prelude operators needed).
    let source = r#"
module Test where

pick :: Boolean -> Int
pick b
  | b = 100
  | true = 200

test :: Int
test = pick false
-- TEST: 200
"#;
    run_fixture("p3_guards", source);
}

#[test]
fn codegen_p3_where_and_let() {
    let source = r#"
module Test where

test :: Int
test =
  let
    a = 42
  in idx a
  where
  idx x = x
-- TEST: 42
"#;
    run_fixture("p3_where_let", source);
}

#[test]
fn codegen_p3_record_pattern() {
    let source = r#"
module Test where

getX :: { x :: Int, y :: Int } -> Int
getX { x } = x

test :: Int
test = getX { x: 42, y: 7 }
-- TEST: 42
"#;
    run_fixture("p3_record_pattern", source);
}

#[test]
fn codegen_p3_as_and_nested() {
    let source = r#"
module Test where

data Tree = Leaf Int | Node Tree Tree

sumLeftmost :: Tree -> Int
sumLeftmost t = case t of
  Node (Leaf n) _ -> n
  Leaf n -> n
  Node _ _ -> 0

test :: Int
test = sumLeftmost (Node (Leaf 42) (Leaf 1))
-- TEST: 42
"#;
    run_fixture("p3_nested", source);
}

#[test]
fn codegen_p2_foreign_import() {
    let source = r#"
module Test where

foreign import double :: Int -> Int

test :: Int
test = double 21
-- TEST: 42
"#;
    let ffi = "export const double = function (x) { return x * 2; };\n";
    run_fixture_ffi("p2_foreign", source, Some(ffi));
}

// ---------------------------------------------------------------------------
// Phase 4: type classes — method dispatch over local instances (concrete)
// ---------------------------------------------------------------------------

#[test]
fn codegen_p4_class_dispatch() {
    let source = r#"
module Test where

class ToInt a where
  toInt :: a -> Int

data Color = Red | Green | Blue

instance ToInt Color where
  toInt Red = 0
  toInt Green = 1
  toInt Blue = 2

test :: Int
test = toInt Green
-- TEST: 1
"#;
    run_fixture("p4_class_dispatch", source);
}

#[test]
fn codegen_p4_class_two_instances() {
    // Two instances of the same class on different types; dispatch must pick
    // the one matching the argument's type.
    let source = r#"
module Test where

class Describe a where
  describe :: a -> Int

data Animal = Cat | Dog
data Plant = Tree

instance Describe Animal where
  describe Cat = 10
  describe Dog = 20

instance Describe Plant where
  describe Tree = 99

test :: Int
test = describe Tree
-- TEST: 99
"#;
    run_fixture("p4_two_instances", source);
}

// ---------------------------------------------------------------------------
// Phase 5: constrained instances (context dicts) + dict params for polymorphic
// functions.
// ---------------------------------------------------------------------------

#[test]
fn codegen_p5_constrained_instance() {
    // `Sz a => Sz (Wrap a)` used at a concrete `Wrap Leaf` → one level of
    // context dict: szWrap(szLeaf).
    let source = r#"
module Test where

class Sz a where
  sz :: a -> Int

data Leaf = Leaf
data Wrap a = Wrap a

instance Sz Leaf where
  sz Leaf = 5

instance Sz a => Sz (Wrap a) where
  sz (Wrap x) = sz x

test :: Int
test = sz (Wrap Leaf)
-- TEST: 5
"#;
    run_fixture("p5_constrained_instance", source);
}

#[test]
fn codegen_p5_polymorphic_fn() {
    // A polymorphic function with a class constraint; the dict is threaded as a
    // leading parameter and passed concretely at the call site.
    let source = r#"
module Test where

class Sz a where
  sz :: a -> Int

data Leaf = Leaf

instance Sz Leaf where
  sz Leaf = 5

twice :: forall a. Sz a => a -> Int
twice x = sz x

test :: Int
test = twice Leaf
-- TEST: 5
"#;
    run_fixture("p5_polymorphic_fn", source);
}

#[test]
fn codegen_p4_method_with_arg() {
    let source = r#"
module Test where

class Combine a where
  combine :: a -> a -> Int

data Pair = Pair Int Int

instance Combine Pair where
  combine (Pair a _) (Pair _ d) = a

test :: Int
test = combine (Pair 42 1) (Pair 2 3)
-- TEST: 42
"#;
    run_fixture("p4_method_arg", source);
}
