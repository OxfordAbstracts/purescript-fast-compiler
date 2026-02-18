//! Codegen integration tests.
//!
//! For each fixture in tests/fixtures/codegen/, compile the PureScript source
//! and generate JavaScript. Tests validate:
//! 1. The module compiles without type errors
//! 2. JS is generated (non-empty)
//! 3. The generated JS is syntactically valid (parseable by SWC)
//! 4. Snapshot tests capture the exact output for review

use purescript_fast_compiler::build::build_from_sources_with_js;
use purescript_fast_compiler::codegen;
use std::collections::HashMap;

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

    // Find the module in the registry and generate JS
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

/// Validate that a JS string is syntactically valid by parsing with SWC.
fn assert_valid_js(js: &str, context: &str) {
    use swc_common::{FileName, SourceMap, sync::Lrc};
    use swc_ecma_parser::{EsSyntax, Parser, StringInput, Syntax};

    let cm: Lrc<SourceMap> = Default::default();
    let fm = cm.new_source_file(
        Lrc::new(FileName::Custom(context.to_string())),
        js.to_string(),
    );

    let mut parser = Parser::new(
        Syntax::Es(EsSyntax {
            import_attributes: true,
            ..Default::default()
        }),
        StringInput::from(&*fm),
        None,
    );

    match parser.parse_module() {
        Ok(_) => {}
        Err(e) => {
            panic!(
                "Generated JS for {} is not valid:\nError: {:?}\n\nJS output:\n{}",
                context, e, js
            );
        }
    }
}

// ===== Fixture tests =====

macro_rules! codegen_test {
    ($name:ident, $file:expr) => {
        #[test]
        fn $name() {
            let source = include_str!(concat!("fixtures/codegen/", $file, ".purs"));
            let js = codegen_fixture(source);
            assert!(!js.is_empty(), "Generated JS should not be empty");
            assert_valid_js(&js, $file);
            insta::assert_snapshot!(concat!("codegen_", $file), js);
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
            assert_valid_js(&js, $file);
            insta::assert_snapshot!(concat!("codegen_", $file), js);
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

// ===== Node.js execution tests =====
// These tests verify that the generated JS actually runs correctly by executing
// it with Node.js and checking assertions via process.exit codes.

/// Generate JS from PureScript, append a test harness, write to a temp file, and run with Node.
fn run_js_with_assertions(purs_source: &str, test_script: &str) {
    let js = codegen_fixture(purs_source);
    assert_valid_js(&js, "run_test");

    // Strip the ES module export line so we can run it as a plain script
    let js_without_exports: String = js
        .lines()
        .filter(|line| !line.starts_with("export {") && !line.starts_with("import "))
        .collect::<Vec<_>>()
        .join("\n");

    let full_script = format!("{js_without_exports}\n\n// Test assertions\n{test_script}");

    let tmp_dir = std::env::temp_dir().join("pfc_test");
    let _ = std::fs::create_dir_all(&tmp_dir);
    static TEST_COUNTER: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let id = TEST_COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let tmp_file = tmp_dir.join(format!("test_{}_{}.mjs", std::process::id(), id));
    std::fs::write(&tmp_file, &full_script).expect("Failed to write temp JS file");

    let output = std::process::Command::new("node")
        .arg(&tmp_file)
        .output()
        .expect("Failed to run node");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    if !output.status.success() {
        let _ = std::fs::remove_file(&tmp_file);
        panic!(
            "Node.js execution failed (exit code {:?}):\n\
             --- stdout ---\n{}\n\
             --- stderr ---\n{}\n\
             --- generated JS ---\n{}",
            output.status.code(),
            stdout,
            stderr,
            full_script
        );
    }

    let _ = std::fs::remove_file(&tmp_file);
}

#[test]
fn node_run_literals() {
    run_js_with_assertions(
        include_str!("fixtures/codegen/RunLiterals.purs"),
        r#"
if (anInt !== 42) throw new Error("anInt should be 42, got " + anInt);
if (aString !== "hello") throw new Error("aString should be hello");
if (aBool !== true) throw new Error("aBool should be true");
if (anArray.length !== 3) throw new Error("anArray should have length 3");
if (anArray[0] !== 1) throw new Error("anArray[0] should be 1");
"#,
    );
}

#[test]
fn node_run_functions() {
    run_js_with_assertions(
        include_str!("fixtures/codegen/RunFunctions.purs"),
        r#"
if (identity(42) !== 42) throw new Error("identity(42) should be 42");
if (identity("hello") !== "hello") throw new Error("identity('hello') should be 'hello'");
if (constFunc(1)(2) !== 1) throw new Error("constFunc(1)(2) should be 1");
if (apply(identity)(99) !== 99) throw new Error("apply(identity)(99) should be 99");
"#,
    );
}

#[test]
fn node_run_patterns() {
    run_js_with_assertions(
        include_str!("fixtures/codegen/RunPatterns.purs"),
        r#"
var n = Nothing.value;
var j = Just.create(42);
if (fromMaybe(0)(n) !== 0) throw new Error("fromMaybe(0)(Nothing) should be 0");
if (fromMaybe(0)(j) !== 42) throw new Error("fromMaybe(0)(Just 42) should be 42");
if (isJust(n) !== false) throw new Error("isJust(Nothing) should be false");
if (isJust(j) !== true) throw new Error("isJust(Just 42) should be true");
"#,
    );
}

#[test]
fn node_run_records() {
    run_js_with_assertions(
        include_str!("fixtures/codegen/RunRecords.purs"),
        r#"
var p = mkPerson("Alice")(30);
if (getName(p) !== "Alice") throw new Error("getName should be Alice");
if (getAge(p) !== 30) throw new Error("getAge should be 30");
if (p.name !== "Alice") throw new Error("p.name should be Alice");
if (p.age !== 30) throw new Error("p.age should be 30");
"#,
    );
}

#[test]
fn node_run_newtype() {
    run_js_with_assertions(
        include_str!("fixtures/codegen/RunNewtype.purs"),
        r#"
var n = mkName("Bob");
if (n !== "Bob") throw new Error("newtype should be erased, got " + JSON.stringify(n));
var unwrapped = unwrapName("Charlie");
if (unwrapped !== "Charlie") throw new Error("unwrapName should pass through, got " + unwrapped);
"#,
    );
}

#[test]
fn node_run_let_where() {
    run_js_with_assertions(
        include_str!("fixtures/codegen/RunLetWhere.purs"),
        r#"
if (letSimple !== 42) throw new Error("letSimple should be 42, got " + letSimple);
if (whereSimple !== 99) throw new Error("whereSimple should be 99, got " + whereSimple);
"#,
    );
}
