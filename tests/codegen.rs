//! Codegen integration tests.
//!
//! For each fixture in tests/fixtures/codegen/, compile the PureScript source
//! and generate JavaScript. Tests validate:
//! 1. The module compiles without type errors
//! 2. JS is generated (non-empty)
//! 3. The generated JS is syntactically valid (parseable by SWC)
//! 4. Snapshot tests capture the exact output for review

use purescript_fast_compiler::build::{build_from_sources_with_js, build_from_sources_with_registry};
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

/// Parse JS, sort exports, and re-emit through SWC codegen for normalized comparison.
/// Strips comments (including `/* #__PURE__ */`), normalizes whitespace, and sorts exports.
fn normalize_js(js: &str) -> String {
    use swc_common::{FileName, SourceMap, sync::Lrc};
    use swc_ecma_parser::{Parser, StringInput, Syntax, EsSyntax};
    use swc_ecma_codegen::{Emitter, text_writer::JsWriter};
    use swc_ecma_ast::*;

    let cm: Lrc<SourceMap> = Default::default();
    let fm = cm.new_source_file(
        Lrc::new(FileName::Custom("normalize".to_string())),
        js.to_string(),
    );

    let mut parser = Parser::new(
        Syntax::Es(EsSyntax::default()),
        StringInput::from(&*fm),
        None,
    );

    let mut module = parser.parse_module().expect("Failed to parse JS for normalization");

    // Sort export specifiers alphabetically
    let export_name = |n: &ExportSpecifier| -> String {
        match n {
            ExportSpecifier::Named(n) => match &n.exported {
                Some(ModuleExportName::Ident(id)) => id.sym.to_string(),
                None => match &n.orig {
                    ModuleExportName::Ident(id) => id.sym.to_string(),
                    _ => String::new(),
                },
                _ => String::new(),
            },
            _ => String::new(),
        }
    };
    for item in &mut module.body {
        if let ModuleItem::ModuleDecl(ModuleDecl::ExportNamed(export)) = item {
            export.specifiers.sort_by(|a, b| export_name(a).cmp(&export_name(b)));
        }
    }

    // Sort imports alphabetically by source path
    let import_src = |item: &ModuleItem| -> Option<String> {
        if let ModuleItem::ModuleDecl(ModuleDecl::Import(import)) = item {
            return Some(import.src.value.to_string_lossy().into_owned());
        }
        None
    };
    let mut import_indices: Vec<usize> = module.body.iter().enumerate()
        .filter_map(|(i, item)| import_src(item).map(|_| i))
        .collect();
    if !import_indices.is_empty() {
        let mut import_items: Vec<ModuleItem> = import_indices.iter()
            .map(|&i| module.body[i].clone())
            .collect();
        import_items.sort_by(|a, b| {
            let na = import_src(a).unwrap_or_default();
            let nb = import_src(b).unwrap_or_default();
            na.cmp(&nb)
        });
        for (slot, item) in import_indices.iter().zip(import_items) {
            module.body[*slot] = item;
        }
    }

    // Sort top-level var declarations alphabetically (ignore declaration order differences)
    // Imports and exports keep their positions, only var decls are sorted among themselves.
    let decl_name = |item: &ModuleItem| -> Option<String> {
        if let ModuleItem::Stmt(Stmt::Decl(Decl::Var(var_decl))) = item {
            if let Some(decl) = var_decl.decls.first() {
                if let Pat::Ident(ident) = &decl.name {
                    return Some(ident.sym.to_string());
                }
            }
        }
        None
    };
    // Collect indices of var decls, sort them, and reinsert
    let mut var_indices: Vec<usize> = module.body.iter().enumerate()
        .filter_map(|(i, item)| decl_name(item).map(|_| i))
        .collect();
    if !var_indices.is_empty() {
        let mut var_items: Vec<ModuleItem> = var_indices.iter()
            .map(|&i| module.body[i].clone())
            .collect();
        var_items.sort_by(|a, b| {
            let na = decl_name(a).unwrap_or_default();
            let nb = decl_name(b).unwrap_or_default();
            na.cmp(&nb)
        });
        for (slot, item) in var_indices.iter().zip(var_items) {
            module.body[*slot] = item;
        }
    }

    // Emit normalized JS
    let mut buf = Vec::new();
    {
        let writer = JsWriter::new(cm.clone(), "\n", &mut buf, None);
        let mut emitter = Emitter {
            cfg: swc_ecma_codegen::Config::default().with_minify(false),
            cm: cm.clone(),
            comments: None,
            wr: writer,
        };
        emitter.emit_module(&module).expect("Failed to emit JS");
    }

    let js = String::from_utf8(buf).expect("Invalid UTF-8 in emitted JS");
    // Strip standalone empty statements (`;` on its own line) — the original compiler
    // adds trailing `;` after `if {}` blocks which SWC preserves as empty statements
    let js: String = js.lines()
        .filter(|line| line.trim() != ";")
        .collect::<Vec<_>>()
        .join("\n");
    // Normalize error messages: replace `throw new Error("Failed pattern match at ..." + [...])`
    // and `throw Error("Failed pattern match")` with a canonical form
    let re = regex::Regex::new(
        r#"throw new Error\("Failed pattern match[^"]*"\s*\+\s*\[[^\]]*\]\)"#
    ).unwrap();
    let js = re.replace_all(&js, r#"throw new Error("Failed pattern match")"#).to_string();
    let re2 = regex::Regex::new(
        r#"throw Error\("Failed pattern match[^"]*"\)"#
    ).unwrap();
    let js = re2.replace_all(&js, r#"throw new Error("Failed pattern match")"#).to_string();
    // Also normalize multiline error concatenation (SWC may split across lines)
    let re3 = regex::Regex::new(
        r#"throw new Error\("Failed pattern match[^"]*"\s*\+\s*\[\s*\n[^\]]*\]\)"#
    ).unwrap();
    let js = re3.replace_all(&js, r#"throw new Error("Failed pattern match")"#).to_string();
    js
}

/// Structured JS module parts for fine-grained comparison.
#[derive(Debug)]
struct JsParts {
    imports: Vec<String>,       // sorted import lines
    declarations: Vec<String>,  // sorted var declaration blocks (name → full text)
    exports: Vec<String>,       // sorted export blocks
}

/// Parse normalized JS into structured parts for comparison.
fn parse_js_parts(normalized_js: &str) -> JsParts {
    use swc_common::{FileName, SourceMap, sync::Lrc};
    use swc_ecma_parser::{Parser, StringInput, Syntax, EsSyntax};
    use swc_ecma_codegen::{Emitter, text_writer::JsWriter};
    use swc_ecma_ast::*;

    let cm: Lrc<SourceMap> = Default::default();
    let fm = cm.new_source_file(
        Lrc::new(FileName::Custom("parts".to_string())),
        normalized_js.to_string(),
    );
    let mut parser = Parser::new(
        Syntax::Es(EsSyntax::default()),
        StringInput::from(&*fm),
        None,
    );
    let module = parser.parse_module().expect("Failed to parse JS for parts extraction");

    let emit_item = |item: &ModuleItem| -> String {
        let cm2: Lrc<SourceMap> = Default::default();
        let mut buf = Vec::new();
        {
            let writer = JsWriter::new(cm2.clone(), "\n", &mut buf, None);
            let mut emitter = Emitter {
                cfg: swc_ecma_codegen::Config::default().with_minify(false),
                cm: cm2.clone(),
                comments: None,
                wr: writer,
            };
            // Wrap in a temporary module to emit
            let tmp = Module {
                span: Default::default(),
                body: vec![item.clone()],
                shebang: None,
            };
            emitter.emit_module(&tmp).expect("emit");
        }
        let s = String::from_utf8(buf).unwrap();
        s.trim().to_string()
    };

    let mut imports = Vec::new();
    let mut declarations = Vec::new();
    let mut exports = Vec::new();

    for item in &module.body {
        match item {
            ModuleItem::ModuleDecl(ModuleDecl::Import(_)) => {
                imports.push(emit_item(item));
            }
            ModuleItem::ModuleDecl(ModuleDecl::ExportNamed(_)) => {
                exports.push(emit_item(item));
            }
            _ => {
                declarations.push(emit_item(item));
            }
        }
    }

    imports.sort();
    declarations.sort();
    exports.sort();

    JsParts { imports, declarations, exports }
}

/// Compare two JS modules structurally, returning a detailed error message per category.
/// Returns None if they match, Some(error_message) if they differ.
fn compare_js_parts(actual_js: &str, expected_js: &str, module_name: &str) -> Option<String> {
    let actual = parse_js_parts(actual_js);
    let expected = parse_js_parts(expected_js);

    let mut errors = Vec::new();

    // 1. Check import count
    if actual.imports.len() != expected.imports.len() {
        let actual_set: std::collections::HashSet<_> = actual.imports.iter().collect();
        let expected_set: std::collections::HashSet<_> = expected.imports.iter().collect();
        let missing: Vec<_> = expected_set.difference(&actual_set).collect();
        let extra: Vec<_> = actual_set.difference(&expected_set).collect();
        let mut msg = format!("  IMPORTS count mismatch: actual={}, expected={}", actual.imports.len(), expected.imports.len());
        if !missing.is_empty() {
            msg.push_str(&format!("\n    missing: {}", missing.iter().map(|s| s.as_str()).collect::<Vec<_>>().join(", ")));
        }
        if !extra.is_empty() {
            msg.push_str(&format!("\n    extra:   {}", extra.iter().map(|s| s.as_str()).collect::<Vec<_>>().join(", ")));
        }
        errors.push(msg);
    } else {
        // 2. Check each import matches
        let mut import_diffs = Vec::new();
        for (a, e) in actual.imports.iter().zip(expected.imports.iter()) {
            if a != e {
                import_diffs.push(format!("    actual:   {}\n    expected: {}", a, e));
            }
        }
        if !import_diffs.is_empty() {
            errors.push(format!("  IMPORTS differ:\n{}", import_diffs.join("\n")));
        }
    }

    // 3. Check declaration count
    if actual.declarations.len() != expected.declarations.len() {
        let actual_names: Vec<String> = actual.declarations.iter()
            .map(|d| d.lines().next().unwrap_or("").chars().take(60).collect())
            .collect();
        let expected_names: Vec<String> = expected.declarations.iter()
            .map(|d| d.lines().next().unwrap_or("").chars().take(60).collect())
            .collect();
        let actual_set: std::collections::HashSet<_> = actual_names.iter().collect();
        let expected_set: std::collections::HashSet<_> = expected_names.iter().collect();
        let missing: Vec<_> = expected_set.difference(&actual_set).collect();
        let extra: Vec<_> = actual_set.difference(&expected_set).collect();
        let mut msg = format!("  DECLARATIONS count mismatch: actual={}, expected={}", actual.declarations.len(), expected.declarations.len());
        if !missing.is_empty() {
            msg.push_str(&format!("\n    missing: {:?}", missing));
        }
        if !extra.is_empty() {
            msg.push_str(&format!("\n    extra:   {:?}", extra));
        }
        errors.push(msg);
    } else {
        // 4. Check each declaration matches
        let mut decl_diffs = Vec::new();
        for (a, e) in actual.declarations.iter().zip(expected.declarations.iter()) {
            if a != e {
                // Find first differing line
                let a_lines: Vec<&str> = a.lines().collect();
                let e_lines: Vec<&str> = e.lines().collect();
                let first_diff = a_lines.iter().zip(e_lines.iter())
                    .enumerate()
                    .find(|(_, (al, el))| al != el)
                    .map(|(i, (al, el))| format!("    line {}: actual:   {}\n    line {}: expected: {}", i+1, al, i+1, el))
                    .unwrap_or_else(|| format!("    length differs: actual {} lines, expected {} lines", a_lines.len(), e_lines.len()));
                let decl_name_a: String = a.lines().next().unwrap_or("").chars().take(60).collect();
                decl_diffs.push(format!("    decl '{}...':\n{}", decl_name_a, first_diff));
            }
        }
        if !decl_diffs.is_empty() {
            errors.push(format!("  DECLARATIONS differ:\n{}", decl_diffs.join("\n")));
        }
    }

    // 5. Check exports
    if actual.exports != expected.exports {
        let mut export_diffs = Vec::new();
        let max = actual.exports.len().max(expected.exports.len());
        for i in 0..max {
            let a = actual.exports.get(i).map(|s| s.as_str()).unwrap_or("<missing>");
            let e = expected.exports.get(i).map(|s| s.as_str()).unwrap_or("<missing>");
            if a != e {
                export_diffs.push(format!("    actual:   {}\n    expected: {}", a.lines().next().unwrap_or(""), e.lines().next().unwrap_or("")));
            }
        }
        if !export_diffs.is_empty() {
            errors.push(format!("  EXPORTS differ:\n{}", export_diffs.join("\n")));
        }
    }

    if errors.is_empty() {
        None
    } else {
        Some(format!("{}:\n{}", module_name, errors.join("\n")))
    }
}

/// Assert that two JS strings are structurally equivalent after normalization.
fn assert_js_matches(actual: &str, expected: &str, context: &str) {
    let norm_actual = normalize_js(actual);
    let norm_expected = normalize_js(expected);
    if norm_actual != norm_expected {
        // Use pretty_assertions-style diff
        let mut diff_lines = Vec::new();
        let actual_lines: Vec<&str> = norm_actual.lines().collect();
        let expected_lines: Vec<&str> = norm_expected.lines().collect();
        let max_lines = actual_lines.len().max(expected_lines.len());
        for i in 0..max_lines {
            let a = actual_lines.get(i).unwrap_or(&"<missing>");
            let e = expected_lines.get(i).unwrap_or(&"<missing>");
            if a != e {
                diff_lines.push(format!("  line {}: actual  : {}", i + 1, a));
                diff_lines.push(format!("  line {}: expected: {}", i + 1, e));
            }
        }
        panic!(
            "Normalized JS mismatch for {}:\n\n{}\n\n--- actual (normalized) ---\n{}\n\n--- expected (normalized) ---\n{}",
            context,
            diff_lines.join("\n"),
            norm_actual,
            norm_expected,
        );
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
            assert_valid_js_syntax(&js, $file);
            insta::assert_snapshot!(concat!("codegen_", $file), js);
            let expected = include_str!(concat!(
                "fixtures/codegen/original-compiler-output/", $file, "/index.js"
            ));
            assert_js_matches(&js, expected, $file);
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
            let expected = include_str!(concat!(
                "fixtures/codegen/original-compiler-output/", $file, "/index.js"
            ));
            assert_js_matches(&js, expected, $file);
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
codegen_test!(codegen_class_with_superclass, "SuperClass");
codegen_test!(codegen_class_multi_param, "MultiParam");

// ===== Multi-module tests =====

macro_rules! codegen_multi_test {
    ($name:ident, $dir:expr, $module:expr) => {
        #[test]
        fn $name() {
            let js = codegen_fixture_multi_dir($dir, $module);
            assert!(!js.is_empty(), "Generated JS should not be empty");
            assert_valid_js_syntax(&js, concat!($dir, "/", $module));
            insta::assert_snapshot!(concat!("codegen_", $module), js);
            let expected = include_str!(concat!(
                "fixtures/codegen/original-compiler-output/", $module, "/index.js"
            ));
            assert_js_matches(&js, expected, concat!($dir, "/", $module));
        }
    };
}

codegen_multi_test!(codegen_imports_basic, "ImportsBasic", "Main");
codegen_multi_test!(codegen_imports_transitive, "ImportsTransitive", "Top");
codegen_multi_test!(codegen_imports_data_types, "ImportsDataTypes", "UseTypes");
codegen_multi_test!(codegen_imports_class_and_instances, "ImportsClassAndInstances", "UseClass");
codegen_multi_test!(codegen_instance_chains, "InstanceChains", "UseShow");

// ===== Prelude package test =====

/// Compile the entire prelude package and compare each module's JS output
/// against the original PureScript compiler output.
#[test]
fn codegen_prelude_package() {
    use std::collections::HashMap as Map;

    let pkg_src = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/packages/prelude/src");
    let original_output = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/codegen/original-compiler-output");

    // Collect all .purs source files
    let mut purs_files = Vec::new();
    collect_purs_files(&pkg_src, &mut purs_files);
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

    // Build all prelude modules (no base registry — prelude IS the base)
    let (result, registry) =
        build_from_sources_with_js(&source_refs, &js_sources_opt, None);

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

    // For each module, generate JS and compare against original compiler output
    let mut pass_count = 0;
    let mut fail_count = 0;
    let mut failures = Vec::new();

    // Build a map of which source files have FFI
    let ffi_files: std::collections::HashSet<String> = purs_files
        .iter()
        .filter(|f| f.with_extension("js").exists())
        .map(|f| f.to_string_lossy().into_owned())
        .collect();

    for (filename, source) in &sources {
        let parsed_module = match purescript_fast_compiler::parse(source) {
            Ok(m) => m,
            Err(_) => continue,
        };
        let module_parts: Vec<_> = parsed_module.name.value.parts.clone();
        let module_name_parts: Vec<String> = module_parts
            .iter()
            .map(|s| purescript_fast_compiler::interner::resolve(*s).unwrap_or_default())
            .collect();
        let module_name = module_name_parts.join(".");

        let exports = match registry.lookup(&module_parts) {
            Some(e) => e,
            None => continue,
        };

        // Check if original compiler output exists for this module
        let expected_path = original_output.join(&module_name).join("index.js");
        let expected_js = match std::fs::read_to_string(&expected_path) {
            Ok(s) => s,
            Err(_) => continue, // No expected output for this module
        };

        let has_ffi = ffi_files.contains(filename);
        let js_module = codegen::js::module_to_js(
            &parsed_module,
            &module_name,
            &module_parts,
            exports,
            &registry,
            has_ffi,
        );
        let js = codegen::printer::print_module(&js_module);

        // Normalize both sides
        let norm_actual = normalize_js(&js);
        let norm_expected = normalize_js(&expected_js);

        // Dump specific modules for debugging
        std::fs::create_dir_all("/tmp/codegen_debug").ok();
        std::fs::write(format!("/tmp/codegen_debug/{}.js", module_name), &js).ok();

        // Structured comparison: imports, declarations, exports
        match compare_js_parts(&norm_actual, &norm_expected, &module_name) {
            None => {
                pass_count += 1;
            }
            Some(error_msg) => {
                fail_count += 1;
                failures.push((module_name.clone(), error_msg));
            }
        }
    }

    if !failures.is_empty() {
        // Build a summary table: module → which categories failed
        let mut import_count_failures = Vec::new();
        let mut import_diff_failures = Vec::new();
        let mut decl_count_failures = Vec::new();
        let mut decl_diff_failures = Vec::new();
        let mut export_failures = Vec::new();

        for (module, msg) in &failures {
            if msg.contains("IMPORTS count mismatch") {
                import_count_failures.push(module.as_str());
            } else if msg.contains("IMPORTS differ") {
                import_diff_failures.push(module.as_str());
            }
            if msg.contains("DECLARATIONS count mismatch") {
                decl_count_failures.push(module.as_str());
            } else if msg.contains("DECLARATIONS differ") {
                decl_diff_failures.push(module.as_str());
            }
            if msg.contains("EXPORTS differ") {
                export_failures.push(module.as_str());
            }
        }

        let mut summary = String::new();
        summary.push_str(&format!("\n=== SUMMARY: {pass_count} passed, {fail_count} failed ===\n"));
        if !import_count_failures.is_empty() {
            summary.push_str(&format!("\nIMPORT COUNT mismatch ({}):\n  {}\n", import_count_failures.len(), import_count_failures.join(", ")));
        }
        if !import_diff_failures.is_empty() {
            summary.push_str(&format!("\nIMPORT CONTENT mismatch ({}):\n  {}\n", import_diff_failures.len(), import_diff_failures.join(", ")));
        }
        if !decl_count_failures.is_empty() {
            summary.push_str(&format!("\nDECLARATION COUNT mismatch ({}):\n  {}\n", decl_count_failures.len(), decl_count_failures.join(", ")));
        }
        if !decl_diff_failures.is_empty() {
            summary.push_str(&format!("\nDECLARATION CONTENT mismatch ({}):\n  {}\n", decl_diff_failures.len(), decl_diff_failures.join(", ")));
        }
        if !export_failures.is_empty() {
            summary.push_str(&format!("\nEXPORT mismatch ({}):\n  {}\n", export_failures.len(), export_failures.join(", ")));
        }

        panic!(
            "Prelude codegen: {pass_count} passed, {fail_count} failed.\n\nDetailed failures:\n{}\n{summary}",
            failures.iter().map(|(_, msg)| msg.as_str()).collect::<Vec<_>>().join("\n\n")
        );
    }

    // Sanity check: we should have tested a reasonable number of modules
    assert!(
        pass_count >= 40,
        "Expected at least 40 prelude modules to pass, got {pass_count}"
    );
}
