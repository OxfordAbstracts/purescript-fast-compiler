//! Codegen integration tests.
//!
//! For each fixture in tests/fixtures/codegen/, compile the PureScript source
//! and generate TypeScript. Tests validate:
//! 1. The module compiles without type errors
//! 2. TS is generated (non-empty)
//! 3. The generated TS is syntactically valid (parseable by SWC)
//! 4. The generated TS typechecks with tsc --noEmit
//! 5. Snapshot tests capture the exact output for review

use purescript_fast_compiler::build::build_from_sources_with_js;
use purescript_fast_compiler::codegen;
use std::collections::HashMap;

/// Build a single-module fixture and return the generated TS text.
fn codegen_fixture(purs_source: &str) -> String {
    codegen_fixture_with_js(purs_source, None)
}

/// Build a single-module fixture with optional FFI JS source.
fn codegen_fixture_with_js(purs_source: &str, js_source: Option<&str>) -> String {
    let sources = vec![("Test.purs", purs_source)];
    let js_sources = js_source.map(|js| {
        let mut m = HashMap::new();
        m.insert("Test.purs", js);
        m
    });

    let (result, registry) =
        build_from_sources_with_js(&sources, &js_sources, None);

    // Check for build errors
    assert!(
        result.build_errors.is_empty(),
        "Build errors: {:?}",
        result
            .build_errors
            .iter()
            .map(|e| e.to_string())
            .collect::<Vec<_>>()
    );

    // Check all modules compiled without type errors
    for module in &result.modules {
        assert!(
            module.type_errors.is_empty(),
            "Type errors in {}: {:?}",
            module.module_name,
            module
                .type_errors
                .iter()
                .map(|e| e.to_string())
                .collect::<Vec<_>>()
        );
    }

    // Find the module in the registry and generate TS
    let module_result = result.modules.first().expect("Expected at least one module");
    let module_name = &module_result.module_name;

    // Re-parse to get the CST (build_from_sources doesn't expose it)
    let parsed_module = purescript_fast_compiler::parse(purs_source).expect("Parse failed");
    let module_parts: Vec<_> = parsed_module.name.value.parts.clone();

    let exports = registry
        .lookup(&module_parts)
        .expect("Module not found in registry");

    let has_ffi = js_source.is_some();
    let js_module = codegen::js::module_to_js(
        &parsed_module,
        module_name,
        &module_parts,
        exports,
        &registry,
        has_ffi,
    );

    codegen::printer::print_module(&js_module)
}

/// Build multiple modules together and return generated TS for each.
/// Sources are `(filename, purs_source)` pairs, e.g. `("Lib.purs", "module Lib where ...")`.
/// Returns a vec of `(module_name, ts_text)`.
fn codegen_fixture_multi(purs_sources: &[(&str, &str)]) -> Vec<(String, String)> {
    let (result, registry) =
        build_from_sources_with_js(purs_sources, &None, None);

    // Check for build errors
    assert!(
        result.build_errors.is_empty(),
        "Build errors: {:?}",
        result
            .build_errors
            .iter()
            .map(|e| e.to_string())
            .collect::<Vec<_>>()
    );

    // Check all modules compiled without type errors
    for module in &result.modules {
        assert!(
            module.type_errors.is_empty(),
            "Type errors in {}: {:?}",
            module.module_name,
            module
                .type_errors
                .iter()
                .map(|e| e.to_string())
                .collect::<Vec<_>>()
        );
    }

    let mut outputs = Vec::new();
    for (filename, source) in purs_sources {
        let parsed_module = purescript_fast_compiler::parse(source).expect("Parse failed");
        let module_parts: Vec<_> = parsed_module.name.value.parts.clone();
        let module_name = result
            .modules
            .iter()
            .find(|m| {
                let parts_str: Vec<String> = module_parts.iter()
                    .map(|s| purescript_fast_compiler::interner::resolve(*s).unwrap_or_default())
                    .collect();
                m.module_name == parts_str.join(".")
            })
            .map(|m| m.module_name.clone())
            .unwrap_or_else(|| filename.replace(".purs", ""));

        let exports = registry
            .lookup(&module_parts)
            .expect("Module not found in registry");

        let js_module = codegen::js::module_to_js(
            &parsed_module,
            &module_name,
            &module_parts,
            exports,
            &registry,
            false,
        );

        outputs.push((module_name, codegen::printer::print_module(&js_module)));
    }

    outputs
}

/// Validate that a TS string is syntactically valid by parsing with SWC in TypeScript mode.
fn assert_valid_ts_syntax(ts: &str, context: &str) {
    use swc_common::{FileName, SourceMap, sync::Lrc};
    use swc_ecma_parser::{Parser, StringInput, Syntax, TsSyntax};

    let cm: Lrc<SourceMap> = Default::default();
    let fm = cm.new_source_file(
        Lrc::new(FileName::Custom(context.to_string())),
        ts.to_string(),
    );

    let mut parser = Parser::new(
        Syntax::Typescript(TsSyntax {
            tsx: false,
            decorators: false,
            ..Default::default()
        }),
        StringInput::from(&*fm),
        None,
    );

    match parser.parse_module() {
        Ok(_) => {}
        Err(e) => {
            panic!(
                "Generated TS for {} is not syntactically valid:\nError: {:?}\n\nTS output:\n{}",
                context, e, ts
            );
        }
    }
}

/// Typecheck a single TS string using tsc --noEmit.
fn assert_typechecks(ts: &str, context: &str) {
    assert_typechecks_multi(&[(context, ts)]);
}

/// Typecheck multiple TS files together using tsc --noEmit.
/// Each entry is (module_name, ts_source). Files are written into a temp directory
/// structure matching the import paths (e.g. "Lib" → Lib/index.ts).
fn assert_typechecks_multi(files: &[(&str, &str)]) {
    use std::io::Write;

    let dir = tempfile::tempdir().expect("Failed to create temp dir");

    // Write each module into ModuleName/index.ts
    for (name, source) in files {
        let module_dir = dir.path().join(name);
        std::fs::create_dir_all(&module_dir).expect("Failed to create module dir");
        let file_path = module_dir.join("index.ts");
        let mut f = std::fs::File::create(&file_path).expect("Failed to create file");
        f.write_all(source.as_bytes()).expect("Failed to write file");
    }

    // Write a tsconfig.json
    let tsconfig = dir.path().join("tsconfig.json");
    std::fs::write(
        &tsconfig,
        r#"{
  "compilerOptions": {
    "strict": false,
    "noEmit": true,
    "target": "ES2020",
    "module": "ES2020",
    "moduleResolution": "bundler",
    "skipLibCheck": true,
    "allowImportingTsExtensions": true
  },
  "include": ["**/*.ts"]
}"#,
    )
    .expect("Failed to write tsconfig");

    let output = std::process::Command::new("npx")
        .arg("tsc")
        .arg("--project")
        .arg(&tsconfig)
        .output()
        .expect("Failed to run tsc");

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        let stdout = String::from_utf8_lossy(&output.stdout);
        let mut all_sources = String::new();
        for (name, source) in files {
            all_sources.push_str(&format!("\n=== {}/index.ts ===\n{}\n", name, source));
        }
        panic!(
            "TypeScript typechecking failed for [{}]:\n\ntsc stdout:\n{}\ntsc stderr:\n{}\n\nGenerated sources:{}",
            files.iter().map(|(n, _)| *n).collect::<Vec<_>>().join(", "),
            stdout,
            stderr,
            all_sources,
        );
    }
}

// ===== Fixture tests =====

macro_rules! codegen_test {
    ($name:ident, $file:expr) => {
        #[test]
        fn $name() {
            let source = include_str!(concat!("fixtures/codegen/", $file, ".purs"));
            let ts = codegen_fixture(source);
            assert!(!ts.is_empty(), "Generated TS should not be empty");
            assert_valid_ts_syntax(&ts, $file);
            assert_typechecks(&ts, $file);
            insta::assert_snapshot!(concat!("codegen_", $file), ts);
        }
    };
}

macro_rules! codegen_test_with_ffi {
    ($name:ident, $file:expr) => {
        #[test]
        fn $name() {
            let source = include_str!(concat!("fixtures/codegen/", $file, ".purs"));
            let js_src = include_str!(concat!("fixtures/codegen/", $file, ".js"));
            let ts = codegen_fixture_with_js(source, Some(js_src));
            assert!(!ts.is_empty(), "Generated TS should not be empty");
            assert_valid_ts_syntax(&ts, $file);
            // Skip tsc for FFI tests (foreign.js won't resolve as TS)
            insta::assert_snapshot!(concat!("codegen_", $file), ts);
        }
    };
}

codegen_test!(codegen_literals, "Literals");
codegen_test!(codegen_functions, "Functions");
codegen_test!(codegen_data_constructors, "DataConstructors");
codegen_test!(codegen_newtype_erasure, "NewtypeErasure");
codegen_test!(codegen_pattern_matching, "PatternMatching");
codegen_test!(codegen_record_ops, "RecordOps");
codegen_test!(codegen_let_and_where, "LetAndWhere");
codegen_test!(codegen_guards, "Guards");
codegen_test!(codegen_case_expressions, "CaseExpressions");
codegen_test!(codegen_negate_and_unary, "NegateAndUnary");
codegen_test!(codegen_reserved_words, "ReservedWords");
codegen_test!(codegen_instance_dictionaries, "InstanceDictionaries");
codegen_test_with_ffi!(codegen_foreign_import, "ForeignImport");
codegen_test!(codegen_do_notation, "DoNotation");
codegen_test!(codegen_operators, "Operators");
codegen_test!(codegen_type_annotations, "TypeAnnotations");
codegen_test!(codegen_type_class_basics, "TypeClassBasics");
codegen_test!(codegen_record_wildcards, "RecordWildcards");
codegen_test!(codegen_where_bindings, "WhereBindings");
codegen_test!(codegen_derive_eq, "DeriveEq");
codegen_test!(codegen_derive_ord, "DeriveOrd");
codegen_test!(codegen_derive_functor, "DeriveFunctor");
codegen_test!(codegen_derive_newtype, "DeriveNewtype");
codegen_test!(codegen_derive_generic, "DeriveGeneric");

// ===== Multi-module tests =====

#[test]
fn codegen_imports_basic() {
    let lib_source = r#"module Lib where

greet :: String -> String
greet name = name

magicNumber :: Int
magicNumber = 42
"#;

    let main_source = r#"module Main where

import Lib (greet, magicNumber)

greeting :: String
greeting = greet "world"

num :: Int
num = magicNumber
"#;

    let outputs = codegen_fixture_multi(&[
        ("Lib.purs", lib_source),
        ("Main.purs", main_source),
    ]);

    let files: Vec<(&str, &str)> = outputs
        .iter()
        .map(|(name, ts)| (name.as_str(), ts.as_str()))
        .collect();

    // Syntax check each file
    for (name, ts) in &files {
        assert_valid_ts_syntax(ts, name);
    }

    // Typecheck all files together
    assert_typechecks_multi(&files);

    // Snapshot the main module
    let main_ts = &outputs.iter().find(|(n, _)| n == "Main").unwrap().1;
    insta::assert_snapshot!("codegen_ImportsBasic", main_ts);
}

#[test]
fn codegen_imports_transitive() {
    let base_source = r#"module Base where

baseValue :: Int
baseValue = 1

identity :: forall a. a -> a
identity x = x
"#;

    let middle_source = r#"module Middle where

import Base (baseValue, identity)

middleValue :: Int
middleValue = identity baseValue
"#;

    let top_source = r#"module Top where

import Middle (middleValue)

topValue :: Int
topValue = middleValue
"#;

    let outputs = codegen_fixture_multi(&[
        ("Base.purs", base_source),
        ("Middle.purs", middle_source),
        ("Top.purs", top_source),
    ]);

    let files: Vec<(&str, &str)> = outputs
        .iter()
        .map(|(name, ts)| (name.as_str(), ts.as_str()))
        .collect();

    for (name, ts) in &files {
        assert_valid_ts_syntax(ts, name);
    }
    assert_typechecks_multi(&files);

    let top_ts = &outputs.iter().find(|(n, _)| n == "Top").unwrap().1;
    insta::assert_snapshot!("codegen_ImportsTransitive", top_ts);
}

#[test]
fn codegen_imports_data_types() {
    let types_source = r#"module Types where

data Color = Red | Green | Blue

data Maybe a = Nothing | Just a
"#;

    let use_source = r#"module UseTypes where

import Types (Color(..), Maybe(..))

isRed :: Color -> Boolean
isRed c = case c of
  Red -> true
  _ -> false

fromMaybe :: forall a. a -> Maybe a -> a
fromMaybe def m = case m of
  Nothing -> def
  Just x -> x
"#;

    let outputs = codegen_fixture_multi(&[
        ("Types.purs", types_source),
        ("UseTypes.purs", use_source),
    ]);

    let files: Vec<(&str, &str)> = outputs
        .iter()
        .map(|(name, ts)| (name.as_str(), ts.as_str()))
        .collect();

    for (name, ts) in &files {
        assert_valid_ts_syntax(ts, name);
    }
    assert_typechecks_multi(&files);

    let use_ts = &outputs.iter().find(|(n, _)| n == "UseTypes").unwrap().1;
    insta::assert_snapshot!("codegen_ImportsDataTypes", use_ts);
}

#[test]
fn codegen_imports_class_and_instances() {
    let class_source = r#"module MyClass where

class MyShow a where
  myShow :: a -> String

instance myShowInt :: MyShow Int where
  myShow _ = "int"

instance myShowString :: MyShow String where
  myShow s = s
"#;

    let use_source = r#"module UseClass where

import MyClass (class MyShow, myShow)

showThing :: forall a. MyShow a => a -> String
showThing x = myShow x

showInt :: String
showInt = myShow 42
"#;

    let outputs = codegen_fixture_multi(&[
        ("MyClass.purs", class_source),
        ("UseClass.purs", use_source),
    ]);

    let files: Vec<(&str, &str)> = outputs
        .iter()
        .map(|(name, ts)| (name.as_str(), ts.as_str()))
        .collect();

    for (name, ts) in &files {
        assert_valid_ts_syntax(ts, name);
    }
    assert_typechecks_multi(&files);

    let use_ts = &outputs.iter().find(|(n, _)| n == "UseClass").unwrap().1;
    insta::assert_snapshot!("codegen_ImportsClassAndInstances", use_ts);
}

#[test]
fn codegen_class_with_superclass() {
    let source = r#"module SuperClass where

class MySemigroup a where
  myAppend :: a -> a -> a

class MySemigroup a <= MyMonoid a where
  myMempty :: a

instance mySemigroupString :: MySemigroup String where
  myAppend a b = a

instance myMonoidString :: MyMonoid String where
  myMempty = ""

useMonoid :: forall a. MyMonoid a => a -> a
useMonoid x = myAppend x myMempty
"#;

    let ts = codegen_fixture(source);
    assert!(!ts.is_empty());
    assert_valid_ts_syntax(&ts, "SuperClass");
    assert_typechecks(&ts, "SuperClass");
    insta::assert_snapshot!("codegen_SuperClass", ts);
}

#[test]
fn codegen_class_multi_param() {
    let source = r#"module MultiParam where

class MyConvert a b where
  myConvert :: a -> b

instance convertIntString :: MyConvert Int String where
  myConvert _ = "int"

doConvert :: forall a b. MyConvert a b => a -> b
doConvert x = myConvert x
"#;

    let ts = codegen_fixture(source);
    assert!(!ts.is_empty());
    assert_valid_ts_syntax(&ts, "MultiParam");
    assert_typechecks(&ts, "MultiParam");
    insta::assert_snapshot!("codegen_MultiParam", ts);
}

#[test]
fn codegen_instance_chains() {
    let class_source = r#"module ShowClass where

class MyShow a where
  myShow :: a -> String

instance myShowInt :: MyShow Int where
  myShow _ = "int"

instance myShowString :: MyShow String where
  myShow s = s

instance myShowBoolean :: MyShow Boolean where
  myShow b = case b of
    true -> "true"
    false -> "false"
"#;

    let use_source = r#"module UseShow where

import ShowClass (class MyShow, myShow)

showInt :: String
showInt = myShow 42

showStr :: String
showStr = myShow "hello"

showBool :: String
showBool = myShow true
"#;

    let outputs = codegen_fixture_multi(&[
        ("ShowClass.purs", class_source),
        ("UseShow.purs", use_source),
    ]);

    let files: Vec<(&str, &str)> = outputs
        .iter()
        .map(|(name, ts)| (name.as_str(), ts.as_str()))
        .collect();

    for (name, ts) in &files {
        assert_valid_ts_syntax(ts, name);
    }
    assert_typechecks_multi(&files);

    let use_ts = &outputs.iter().find(|(n, _)| n == "UseShow").unwrap().1;
    insta::assert_snapshot!("codegen_InstanceChains", use_ts);
}
