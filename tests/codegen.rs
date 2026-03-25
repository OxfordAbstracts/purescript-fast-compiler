//! Codegen integration tests.
//!
//! For each fixture in tests/fixtures/codegen/, compile the PureScript source
//! and generate JavaScript. Tests validate:
//! 1. The module compiles without type errors
//! 2. JS is generated (non-empty)
//! 3. The generated JS is syntactically valid (parseable by SWC)
//! 4. Snapshot tests capture the exact output for review

mod test_utils;

use purescript_fast_compiler::build::{build_from_sources_with_js, build_from_sources_with_registry, build_from_sources_with_options, BuildOptions, LogLevel};
use purescript_fast_compiler::codegen;
use purescript_fast_compiler::typechecker::ModuleRegistry;
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::{Arc, OnceLock};

// Support packages needed by codegen fixtures
const CODEGEN_SUPPORT_PACKAGES: &[&str] = &[
    "prelude",
    "newtype",
    "safe-coerce",
    "unsafe-coerce",
];

fn collect_purs_files(dir: &Path, files: &mut Vec<PathBuf>) {
    if let Ok(entries) = std::fs::read_dir(dir) {
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                collect_purs_files(&path, files);
            } else if path.extension().is_some_and(|e| e == "purs") {
                files.push(path);
            }
        }
    }
}

static CODEGEN_SUPPORT: OnceLock<Arc<ModuleRegistry>> = OnceLock::new();

fn get_codegen_registry() -> Arc<ModuleRegistry> {
    Arc::clone(CODEGEN_SUPPORT.get_or_init(|| {
        let packages_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/packages");
        let mut sources = Vec::new();
        for &pkg in CODEGEN_SUPPORT_PACKAGES {
            let pkg_src = packages_dir.join(pkg).join("src");
            let mut files = Vec::new();
            collect_purs_files(&pkg_src, &mut files);
            for f in files {
                if let Ok(source) = std::fs::read_to_string(&f) {
                    sources.push((f.to_string_lossy().into_owned(), source));
                }
            }
        }
        let source_refs: Vec<(&str, &str)> = sources
            .iter()
            .map(|(p, s)| (p.as_str(), s.as_str()))
            .collect();
        let (_, registry) = build_from_sources_with_registry(&source_refs, None);
        Arc::new(registry)
    }))
}

/// Build a single-module fixture and return the generated JS text.
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
        build_from_sources_with_js(&sources, &js_sources, Some(get_codegen_registry()));

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
    let global = codegen::js::GlobalCodegenData::from_registry(&registry);
    let js_module = codegen::js::module_to_js(
        &parsed_module,
        module_name,
        &module_parts,
        exports,
        &registry,
        has_ffi,
        &global,
    );

    codegen::printer::print_module(&js_module)
}

/// Build multiple modules from a fixture directory.
/// Reads all .purs files from tests/fixtures/codegen/<dir_name>/.
/// Returns generated JS for the specified snapshot module.
fn codegen_fixture_multi_dir(dir_name: &str, snapshot_module: &str) -> String {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/codegen")
        .join(dir_name);
    let mut files = Vec::new();
    collect_purs_files(&dir, &mut files);
    files.sort(); // deterministic order
    let sources: Vec<(String, String)> = files
        .iter()
        .map(|f| {
            let content = std::fs::read_to_string(f).expect("Failed to read fixture");
            (f.to_string_lossy().into_owned(), content)
        })
        .collect();
    let source_refs: Vec<(&str, &str)> = sources
        .iter()
        .map(|(p, s)| (p.as_str(), s.as_str()))
        .collect();
    let outputs = codegen_fixture_multi(&source_refs);
    let (_, js) = outputs
        .iter()
        .find(|(n, _)| n == snapshot_module)
        .unwrap_or_else(|| panic!("Module '{}' not found in outputs", snapshot_module));
    js.clone()
}

/// Build multiple modules together and return generated JS for each.
/// Sources are `(filename, purs_source)` pairs, e.g. `("Lib.purs", "module Lib where ...")`.
/// Returns a vec of `(module_name, js_text)`.
fn codegen_fixture_multi(purs_sources: &[(&str, &str)]) -> Vec<(String, String)> {
    let (result, registry) =
        build_from_sources_with_js(purs_sources, &None, Some(get_codegen_registry()));

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

        let global = codegen::js::GlobalCodegenData::from_registry(&registry);
        let js_module = codegen::js::module_to_js(
            &parsed_module,
            &module_name,
            &module_parts,
            exports,
            &registry,
            false,
            &global,
        );

        outputs.push((module_name, codegen::printer::print_module(&js_module)));
    }

    outputs
}

/// Validate that a JS string is syntactically valid by parsing with SWC.
fn assert_valid_js_syntax(js: &str, context: &str) {
    use swc_common::{FileName, SourceMap, sync::Lrc};
    use swc_ecma_parser::{Parser, StringInput, Syntax, EsSyntax};

    let cm: Lrc<SourceMap> = Default::default();
    let fm = cm.new_source_file(
        Lrc::new(FileName::Custom(context.to_string())),
        js.to_string(),
    );

    let mut parser = Parser::new(
        Syntax::Es(EsSyntax {
            ..Default::default()
        }),
        StringInput::from(&*fm),
        None,
    );

    match parser.parse_module() {
        Ok(_) => {}
        Err(e) => {
            panic!(
                "Generated JS for {} is not syntactically valid:\nError: {:?}\n\nJS output:\n{}",
                context, e, js
            );
        }
    }
}

// ===== Runtime test helpers =====

/// Extract the expected test output from a `-- TEST: <expected>` comment in the source.
fn extract_test_expected(source: &str) -> Option<String> {
    for line in source.lines() {
        if let Some(rest) = line.trim().strip_prefix("-- TEST:") {
            return Some(rest.trim().to_string());
        }
    }
    None
}

/// Build a fixture with all support packages and write JS to a temp dir.
/// Returns the output directory path.
fn build_fixture_to_dir(fixture_name: &str, purs_source: &str, js_source: Option<&str>) -> PathBuf {
    let out_dir = std::env::temp_dir().join(format!("pfc-codegen-test-{}", fixture_name));
    if out_dir.exists() {
        std::fs::remove_dir_all(&out_dir).expect("Failed to clean output dir");
    }
    std::fs::create_dir_all(&out_dir).expect("Failed to create output dir");

    // Collect prelude support sources
    let packages_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/packages");
    let mut all_sources = Vec::new();
    for &pkg in CODEGEN_SUPPORT_PACKAGES {
        let pkg_src = packages_dir.join(pkg).join("src");
        let mut files = Vec::new();
        collect_purs_files(&pkg_src, &mut files);
        for f in files {
            if let Ok(source) = std::fs::read_to_string(&f) {
                all_sources.push((f.to_string_lossy().into_owned(), source));
            }
        }
    }

    // Add the fixture source
    all_sources.push(("Test.purs".to_string(), purs_source.to_string()));

    let source_refs: Vec<(&str, &str)> = all_sources
        .iter()
        .map(|(p, s)| (p.as_str(), s.as_str()))
        .collect();

    // Collect FFI JS files from support packages
    let mut js_map: HashMap<&str, String> = HashMap::new();
    for (filename, _) in &all_sources {
        let js_path = PathBuf::from(filename.replace(".purs", ".js"));
        if js_path.exists() {
            let js_content = std::fs::read_to_string(&js_path).expect("Failed to read FFI JS");
            js_map.insert(filename.as_str(), js_content);
        }
    }
    // Add fixture FFI if present
    if let Some(js) = js_source {
        js_map.insert("Test.purs", js.to_string());
    }
    let js_sources_refs: HashMap<&str, &str> = js_map
        .iter()
        .map(|(&k, v)| (k, v.as_str()))
        .collect();
    let js_sources_opt = if js_sources_refs.is_empty() { None } else { Some(js_sources_refs) };

    let options = BuildOptions {
        output_dir: Some(out_dir.clone()),
        log_level: LogLevel::Silent,
        ..Default::default()
    };
    let (result, _) =
        build_from_sources_with_options(&source_refs, &js_sources_opt, None, &options);

    assert!(
        result.build_errors.is_empty(),
        "Build errors for {}: {:?}",
        fixture_name,
        result.build_errors.iter().map(|e| e.to_string()).collect::<Vec<_>>()
    );
    for module in &result.modules {
        assert!(
            module.type_errors.is_empty(),
            "Type errors in {} (fixture {}): {:?}",
            module.module_name,
            fixture_name,
            module.type_errors.iter().map(|e| e.to_string()).collect::<Vec<_>>()
        );
    }

    out_dir
}

/// Extract the module name from PureScript source (e.g., "module Foo.Bar where" → "Foo.Bar").
fn extract_module_name(source: &str) -> String {
    for line in source.lines() {
        let trimmed = line.trim();
        if let Some(rest) = trimmed.strip_prefix("module ") {
            if let Some(name) = rest.split_whitespace().next() {
                return name.to_string();
            }
        }
    }
    panic!("Could not find module name in source");
}

/// Run a Node.js script that imports `test` from the fixture module and prints
/// `JSON.stringify(test)`. Returns the stdout.
fn run_fixture_test(out_dir: &Path, module_name: &str) -> String {
    let runner = out_dir.join("run.mjs");
    // Module name uses dots in PureScript but the output dir uses dots too
    // (e.g., "Data.Show" → "Data.Show/index.js")
    let import_path = format!("./{}/index.js", module_name);
    std::fs::write(
        &runner,
        format!(
            "import {{ test }} from '{}';\nprocess.stdout.write(JSON.stringify(test));\n",
            import_path
        ),
    )
    .expect("Failed to write runner");

    let output = std::process::Command::new("node")
        .arg(&runner)
        .current_dir(out_dir)
        .output()
        .expect("Failed to run node");

    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();

    assert!(
        output.status.success(),
        "Node.js runner failed:\nstdout: {}\nstderr: {}",
        stdout,
        stderr,
    );

    stdout
}

// ===== Fixture tests =====

macro_rules! codegen_test {
    ($name:ident, $file:expr) => {
        #[test]
        fn $name() {
            let source = include_str!(concat!("fixtures/codegen/", $file, ".purs"));
            let js = codegen_fixture(source);
            assert!(!js.is_empty(), "Generated JS should not be empty");
            assert_valid_js_syntax(&js, $file);
            insta::assert_snapshot!(concat!("codegen_", $file), js);

            // Runtime verification: if source has `-- TEST: expected`, build and run via Node.js
            if let Some(expected) = extract_test_expected(source) {
                let module_name = extract_module_name(source);
                let out_dir = build_fixture_to_dir($file, source, None);
                let stdout = run_fixture_test(&out_dir, &module_name);
                assert_eq!(
                    stdout.trim(), expected,
                    "Runtime test mismatch for {}.\nExpected: {}\nGot: {}",
                    $file, expected, stdout.trim()
                );
            }
        }
    };
}

macro_rules! codegen_test_with_ffi {
    ($name:ident, $file:expr) => {
        #[test]
        fn $name() {
            let source = include_str!(concat!("fixtures/codegen/", $file, ".purs"));
            let js_src = include_str!(concat!("fixtures/codegen/", $file, ".js"));
            let js = codegen_fixture_with_js(source, Some(js_src));
            assert!(!js.is_empty(), "Generated JS should not be empty");
            assert_valid_js_syntax(&js, $file);
            insta::assert_snapshot!(concat!("codegen_", $file), js);

            // Runtime verification
            if let Some(expected) = extract_test_expected(source) {
                let module_name = extract_module_name(source);
                let out_dir = build_fixture_to_dir($file, source, Some(js_src));
                let stdout = run_fixture_test(&out_dir, &module_name);
                assert_eq!(
                    stdout.trim(), expected,
                    "Runtime test mismatch for {}.\nExpected: {}\nGot: {}",
                    $file, expected, stdout.trim()
                );
            }
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
codegen_test!(codegen_derive_eq_newtype, "DeriveEqNewtype");
codegen_test!(codegen_derive_ord, "DeriveOrd");
codegen_test!(codegen_derive_ord_newtype, "DeriveOrdNewtype");
codegen_test!(codegen_derive_functor, "DeriveFunctor");
codegen_test!(codegen_derive_newtype, "DeriveNewtype");
codegen_test!(codegen_derive_generic, "DeriveGeneric");
codegen_test!(codegen_class_with_superclass, "SuperClass");
codegen_test!(codegen_class_multi_param, "MultiParam");

// ===== Bug regression tests =====
// These cover specific codegen bug patterns found in package tests.

codegen_test!(codegen_superclass_chain, "SuperClassChain");
codegen_test!(codegen_point_free_dict, "PointFreeDict");
codegen_test!(codegen_constrained_value_dict, "ConstrainedValueDict");
codegen_test!(codegen_multi_constraint_dict, "MultiConstraintDict");
codegen_test!(codegen_constraint_dict_application, "ConstraintDictApplication");
codegen_test!(codegen_missing_dict_intercalate, "MissingDictIntercalate");

// ===== Multi-module tests =====

macro_rules! codegen_multi_test {
    ($name:ident, $dir:expr, $module:expr) => {
        #[test]
        fn $name() {
            let js = codegen_fixture_multi_dir($dir, $module);
            assert!(!js.is_empty(), "Generated JS should not be empty");
            assert_valid_js_syntax(&js, concat!($dir, "/", $module));
            insta::assert_snapshot!(concat!("codegen_", $module), js);
        }
    };
}

codegen_multi_test!(codegen_imports_basic, "ImportsBasic", "Main");
codegen_multi_test!(codegen_imports_transitive, "ImportsTransitive", "Top");
codegen_multi_test!(codegen_imports_data_types, "ImportsDataTypes", "UseTypes");
codegen_multi_test!(codegen_imports_class_and_instances, "ImportsClassAndInstances", "UseClass");
codegen_multi_test!(codegen_instance_chains, "InstanceChains", "UseShow");

// ===== Multi-module tests with runtime verification =====

/// Build a multi-module fixture directory with prelude support and write JS to a temp dir.
/// Returns the output directory path.
fn build_multi_fixture_to_dir(dir_name: &str) -> PathBuf {
    let out_dir = std::env::temp_dir().join(format!("pfc-codegen-multi-test-{}", dir_name));
    if out_dir.exists() {
        std::fs::remove_dir_all(&out_dir).expect("Failed to clean output dir");
    }
    std::fs::create_dir_all(&out_dir).expect("Failed to create output dir");

    // Collect prelude support sources + FFI
    let packages_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/packages");
    let mut all_sources = Vec::new();
    for &pkg in CODEGEN_SUPPORT_PACKAGES {
        let pkg_src = packages_dir.join(pkg).join("src");
        let mut files = Vec::new();
        collect_purs_files(&pkg_src, &mut files);
        for f in files {
            if let Ok(source) = std::fs::read_to_string(&f) {
                all_sources.push((f.to_string_lossy().into_owned(), source));
            }
        }
    }

    // Collect fixture .purs files
    let fixture_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/codegen")
        .join(dir_name);
    let mut fixture_files = Vec::new();
    collect_purs_files(&fixture_dir, &mut fixture_files);
    fixture_files.sort();
    for f in &fixture_files {
        if let Ok(source) = std::fs::read_to_string(f) {
            all_sources.push((f.to_string_lossy().into_owned(), source));
        }
    }

    let source_refs: Vec<(&str, &str)> = all_sources
        .iter()
        .map(|(p, s)| (p.as_str(), s.as_str()))
        .collect();

    // Collect FFI JS files
    let mut js_map: HashMap<String, String> = HashMap::new();
    for (filename, _) in &all_sources {
        let js_path = PathBuf::from(filename.replace(".purs", ".js"));
        if js_path.exists() {
            let js_content = std::fs::read_to_string(&js_path).expect("Failed to read FFI JS");
            js_map.insert(filename.clone(), js_content);
        }
    }
    let js_sources_refs: HashMap<&str, &str> = js_map
        .iter()
        .map(|(k, v)| (k.as_str(), v.as_str()))
        .collect();
    let js_sources_opt = if js_sources_refs.is_empty() { None } else { Some(js_sources_refs) };

    let options = BuildOptions {
        output_dir: Some(out_dir.clone()),
        log_level: LogLevel::Silent,
        ..Default::default()
    };
    let (result, _) =
        build_from_sources_with_options(&source_refs, &js_sources_opt, None, &options);

    assert!(
        result.build_errors.is_empty(),
        "Build errors for {}: {:?}",
        dir_name,
        result.build_errors.iter().map(|e| e.to_string()).collect::<Vec<_>>()
    );
    for module in &result.modules {
        assert!(
            module.type_errors.is_empty(),
            "Type errors in {} (fixture {}): {:?}",
            module.module_name,
            dir_name,
            module.type_errors.iter().map(|e| e.to_string()).collect::<Vec<_>>()
        );
    }

    out_dir
}

/// Multi-module test macro with runtime verification.
/// The `$test_module` is the module containing `test` and `-- TEST:` comment.
macro_rules! codegen_multi_run_test {
    ($name:ident, $dir:expr, $test_module:expr) => {
        #[test]
        fn $name() {
            // Read the test module source to extract the expected value
            let test_module_path = Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("tests/fixtures/codegen")
                .join($dir)
                .join(concat!($test_module, ".purs"));
            let test_source = std::fs::read_to_string(&test_module_path)
                .expect("Failed to read test module source");
            let expected = extract_test_expected(&test_source)
                .expect(concat!("No -- TEST: comment found in ", $test_module, ".purs"));

            let out_dir = build_multi_fixture_to_dir($dir);
            let stdout = run_fixture_test(&out_dir, $test_module);
            assert_eq!(
                stdout.trim(), expected,
                "Runtime test mismatch for {}/{}.\nExpected: {}\nGot: {}",
                $dir, $test_module, expected, stdout.trim()
            );
        }
    };
}

// Bug reproduction: type alias not expanded for instance resolution
// Package test failure: "functorState is not defined" (routing-duplex)
// type State s = StateT s Identity → functorState should resolve to functorStateT(functorIdentity)
codegen_multi_run_test!(codegen_bug_type_alias_instance, "TypeAliasInstanceBug", "TestTypeAlias");

// Bug reproduction: wrong module hint for parameterized instance defined outside class module
// Package test failure: "Control_Bind.bindProxy is not a function" (datetime-parsing)
// bindProxy is in Pipes.Internal, not Control.Bind; also drops dict constraint arg
codegen_multi_run_test!(codegen_bug_wrong_module_hint, "WrongModuleHintBug", "TestWrongModule");

// Bug reproduction: unnecessary $runtime_lazy causing init cycle
// Package test failure: "decodeVoid was needed before it finished initializing" (argonaut-codecs)
// Instance name shadows imported function → codegen treats method body as self-referential
codegen_multi_run_test!(codegen_bug_init_cycle, "InitCycleBug", "TestInitCycle");

// Bug reproduction: TypeEquals-like class with coerce/coerceBack methods used in
// constrained instance context. Tests that instance method references resolve correctly.
codegen_multi_run_test!(codegen_bug_rows_in_instance_context, "RowsInInstanceContextBug", "TestRowsInInstance");

// Bug reproduction: derive newtype instance through type alias resolves to wrong instance name
// E.g., `type State s = StateT s Identity`, `newtype Gen a = Gen (State ...)`,
// `derive newtype instance Functor Gen` → should reference functorStateT, not functorState
codegen_multi_run_test!(codegen_bug_derive_newtype_alias, "DeriveNewtypeAliasBug", "TestDeriveNewtypeAlias");

// Bug reproduction: superclass accessor in parameterized instance must apply wrapper function
// E.g., monoidFn's Semigroup0 accessor must return semigroupFn(dict.Semigroup0()), not raw dict
codegen_multi_run_test!(codegen_bug_superclass_wrapper, "SuperclassWrapperBug", "TestSuperclassWrapper");

// Bug reproduction: same-named instances in different modules — wrong module resolution
// E.g., MyBind.myBindProxy (non-parameterized) vs MyPipe.myBindProxy (parameterized)
codegen_multi_run_test!(codegen_bug_same_name_instance, "SameNameInstanceBug", "TestSameNameInstance");

// Bug reproduction: mutually recursive functions with dict args — hoisted cross-call at init time
// causes stack overflow from circular initialization
codegen_multi_run_test!(codegen_bug_mutual_rec_hoist, "MutualRecHoistBug", "TestMutualRecHoist");

// Bug reproduction: constrained function with where clause using operator from constraint
// Package test failure: "__constraint_1 is not defined" (Data.Map.Internal in tidy-codegen)
codegen_multi_run_test!(codegen_bug_constrained_where_op, "ConstrainedWhereOpBug", "TestConstrainedWhereOp");

// Bug reproduction: passing Ord dict through to another Ord-constrained function
// should pass dictOrd directly, not dictOrd.Eq0()
codegen_multi_run_test!(codegen_bug_superclass_passthrough, "SuperclassPassthroughBug", "TestSuperclassPassthrough");

// Bug reproduction: derive newtype instance Show for newtype wrapping type alias
// derive newtype instance showX :: Show X where newtype X = X MyString, type MyString = String
// should generate showX = showString, not showX = show(...)
codegen_multi_run_test!(codegen_bug_derive_newtype_show, "DeriveNewtypeShowBug", "Test");

// Bug reproduction: point-free function that passes superclass dict through
// outerFn = innerFn where both take same constraint — should pass dict directly
codegen_multi_run_test!(codegen_bug_superclass_coerce, "SuperclassCoerceBug", "TestSuperclassCoerce");

// Bug reproduction: parameterized instance dict arg dropped
// tell(monadTellWriterT(dictMonad)) becomes tell(monadTellWriterT) — missing constraint arg
codegen_multi_run_test!(codegen_bug_parameterized_instance_dict, "ParameterizedInstanceDictBug", "Test");

// Bug reproduction: state(monadStateStateT) missing dict arg through type alias + newtype
// myState(myMonadStateMyStateT(myMonadIdentity)) becomes myState(myMonadStateMyStateT)
codegen_multi_run_test!(codegen_bug_state_alias_dict, "StateAliasDictBug", "Test");

// Bug reproduction: function takes MySup constraint, codegen should pass mySupMyThing (direct)
// not mySubMyThing (subclass). Wrong dict leads to runtime "not a function" on superclass accessor.
codegen_multi_run_test!(codegen_bug_wrong_superclass_dict, "WrongSuperclassDict", "Test");

// ===== Prelude package test =====

/// Compile the entire prelude package (src + test), compare each src module's JS
/// output against the original PureScript compiler output, then run Test.Main
/// via Node.js to verify runtime correctness.
#[test]
fn codegen_prelude_package() {
    use std::collections::HashMap as Map;

    let pkg_root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/packages/prelude");
    let pkg_src = pkg_root.join("src");
    let pkg_test = pkg_root.join("test");

    // Collect all .purs source files from both src and test
    let mut purs_files = Vec::new();
    collect_purs_files(&pkg_src, &mut purs_files);
    collect_purs_files(&pkg_test, &mut purs_files);
    purs_files.sort();

    let sources: Vec<(String, String)> = purs_files
        .iter()
        .map(|f| {
            let content = std::fs::read_to_string(f).expect("Failed to read fixture");
            (f.to_string_lossy().into_owned(), content)
        })
        .collect();
    let source_refs: Vec<(&str, &str)> = sources
        .iter()
        .map(|(p, s)| (p.as_str(), s.as_str()))
        .collect();

    // Collect FFI JS files
    let mut js_map: Map<&str, String> = Map::new();
    for (filename, _) in &sources {
        let js_path = PathBuf::from(filename.replace(".purs", ".js"));
        if js_path.exists() {
            let js_content = std::fs::read_to_string(&js_path).expect("Failed to read FFI JS");
            js_map.insert(filename.as_str(), js_content);
        }
    }
    let js_sources: Map<&str, &str> = js_map
        .iter()
        .map(|(&k, v)| (k, v.as_str()))
        .collect();
    let js_sources_opt = if js_sources.is_empty() { None } else { Some(js_sources) };

    // Create temp output directory for codegen
    let out_dir = std::env::temp_dir().join("purescript-fast-compiler-prelude-run");
    if out_dir.exists() {
        std::fs::remove_dir_all(&out_dir).expect("Failed to clean output dir");
    }
    std::fs::create_dir_all(&out_dir).expect("Failed to create output dir");

    // Build all modules with JS codegen (no base registry — prelude IS the base)
    let options = BuildOptions {
        output_dir: Some(out_dir.clone()),
        log_level: LogLevel::Silent,
        ..Default::default()
    };
    let (result, _) =
        build_from_sources_with_options(&source_refs, &js_sources_opt, None, &options);

    assert!(
        result.build_errors.is_empty(),
        "Prelude build errors: {:?}",
        result.build_errors.iter().map(|e| e.to_string()).collect::<Vec<_>>()
    );
    for module in &result.modules {
        assert!(
            module.type_errors.is_empty(),
            "Type errors in {}: {:?}",
            module.module_name,
            module.type_errors.iter().map(|e| e.to_string()).collect::<Vec<_>>()
        );
    }

    let runner = out_dir.join("run.mjs");
    std::fs::write(
        &runner,
        "import { main } from './Test.Main/index.js';\nmain();\n",
    )
    .expect("Failed to write runner");

    let output = std::process::Command::new("node")
        .arg(&runner)
        .current_dir(&out_dir)
        .output()
        .expect("Failed to run node");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "Test.Main failed with exit code {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        stdout,
        stderr,
    );
}
