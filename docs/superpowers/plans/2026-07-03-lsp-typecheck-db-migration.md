# LSP → typecheck_db Migration Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make `src/lsp/` depend only on `crate::typecheck_db`, removing every `crate::typechecker` reference while preserving all current LSP behaviour.

**Architecture:** Grow `typecheck_db` with two IDE capabilities (span→type recording; unused-import/name warnings) and surface kinds on exports (Part A); add one single-module IDE entry point `check_module_ide` (Part B); rewire the LSP handlers feature-by-feature onto the new backend (Part C). The old typechecker stays in the crate for its non-LSP callers.

**Tech Stack:** Rust, `tower-lsp`, `tokio`, `rusqlite` (via `typecheck_db::store`), `blake3`, the in-crate `parser`/`cst`/`typecheck_db` modules.

## Global Constraints

- The old engine `crate::typechecker` is **not** deleted; only `src/lsp/` stops referencing it. Other callers (`build::build_cached`, the `compile` command, existing tests) keep working.
- **Always-on** span-types and warnings: they are produced whenever a module's inference actually runs. They are **transient** — never written to the SQLite cache and never folded into any cache key (`input_hash`/`output_hash` unchanged).
- Span-types and warnings from a **cache-hit** decl are not produced (its inference is skipped). The LSP entry point (`check_module_ide`) therefore forces full re-inference of the focused module.
- Regression bar: `cargo test --test lsp_e2e` (31 tests) stays green from Part C onward, and `cargo test --lib` (typecheck_db suite) stays green throughout.
- Commit after every task. Branch is `typecheck-db` (already checked out).
- Design doc: `docs/superpowers/specs/2026-07-03-lsp-typecheck-db-migration-design.md`.

## File Structure

**Part A / B (typecheck_db):**
- `src/typecheck_db/unify.rs` — add span-type sidecar to `UnifyState` (struct at `:234`).
- `src/typecheck_db/passes/infer_value.rs` — record spans in `infer_expr` (`:364`), `infer_record` (`:2714`), `infer_record_access` (`:2756`); drain in `infer_value_scc_with_all` (`:968`) mirroring `take_pending_exhaust` (`:1354`).
- `src/typecheck_db/passes/warnings.rs` — **new** — `Warning`/`WarningKind` types + unused-import/name diff.
- `src/typecheck_db/passes/imports.rs` — expose the imported-name → span set for the diff.
- `src/typecheck_db/passes/instance_index.rs` — extend `ClassInfo` (`:64`) with a renderable kind per param.
- `src/typecheck_db/module_registry.rs` — carry per-type/class kind on `ModuleExports` (kind computed near `:451`).
- `src/typecheck_db/driver_multi.rs` — add `span_types` + `warnings` to `ModuleCheckResult` (`:53`, constructors `:110` and `:3354`); add `pub fn check_module_ide` near the entry points (`:194`).
- `src/typecheck_db/tests/mod.rs` — register `mod ide;`.
- `src/typecheck_db/tests/ide.rs` — **new** — unit tests for A2/A3/A4/B1.

**Part C (LSP):**
- `src/lsp/mod.rs` — `Backend` state: registry type + `db` field.
- `src/lsp/handlers/load_sources.rs` — project load via persistent `TypecheckDb`.
- `src/lsp/handlers/diagnostics.rs` — `check_module_ide` + error/warning mapping.
- `src/lsp/handlers/hover.rs` — span-types + registry schemes + kinds.
- `src/lsp/handlers/code_action.rs` — warnings.
- `src/lsp/utils/resolve.rs` — new prim + `module_exports_to_resolved_names`.

## Test harness reference (typecheck_db)

`src/typecheck_db/tests/harness.rs` provides (used by new tests in `ide.rs`):
- `parse_source(src: &str) -> cst::Module`
- `module_name(m: &cst::Module) -> String`
- `check_many_modules(Vec<ModuleInput>) -> ModuleCheckReport` (fresh in-memory db)
- `run_with_shared_db(&mut TypecheckDb, &[(&str, &str)]) -> ...` (see `incremental.rs` for the persistent-db pattern)

`ModuleInput::new(name, src, module)`, `ModuleCheckReport { registry, results, errors }`, `ModuleCheckResult` fields are in `driver_multi.rs:53`.

Helper to reuse in `ide.rs` tests (define once at top of the file):

```rust
use crate::parser::parse;
use crate::typecheck_db::driver_multi::{check_many_modules, ModuleInput, ModuleCheckResult};

/// Parse + check a single module in a fresh in-memory db.
fn check_one(name: &str, src: &str) -> ModuleCheckResult {
    let module = parse(src).expect("parse");
    let report = check_many_modules(vec![ModuleInput::new(name, src, module)]);
    report.results.into_iter().find(|r| r.name == name).expect("result for module")
}

/// Byte offset of the first occurrence of `needle` in `src`.
fn offset_of(src: &str, needle: &str) -> usize {
    src.find(needle).unwrap_or_else(|| panic!("`{needle}` not found in source"))
}
```

---

## Phase A — Grow typecheck_db

### Task A1: Add `span_types` + `warnings` fields to `ModuleCheckResult` (plumbing)

Foundation task: introduce the fields and the `Warning` type wiring so later tasks fill them. No behaviour change yet.

**Files:**
- Create: `src/typecheck_db/passes/warnings.rs`
- Modify: `src/typecheck_db/passes/mod.rs` (register the module), `src/typecheck_db/driver_multi.rs:53-142` and `:3354`
- Test: existing `cargo test --lib` must still pass

**Interfaces:**
- Produces: `crate::typecheck_db::passes::warnings::{Warning, WarningKind}`; new fields `ModuleCheckResult.span_types: std::collections::HashMap<crate::span::Span, crate::typecheck_db::types::Type>` and `ModuleCheckResult.warnings: Vec<Warning>`.

- [ ] **Step 1: Create the warning type**

Create `src/typecheck_db/passes/warnings.rs`:

```rust
//! IDE/compiler warnings (non-fatal). Unlike the error channels these do
//! NOT mark a module as errored (see `ModuleCheckResult::has_errors`), so a
//! module with only warnings is still memoized/clean.

use crate::span::Span;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Warning {
    pub span: Span,
    pub kind: WarningKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WarningKind {
    /// An imported name is never referenced in the module body.
    UnusedImport { name: String },
    /// A let-binding or lambda parameter is never referenced.
    UnusedName { name: String },
}
```

- [ ] **Step 2: Register the module**

In `src/typecheck_db/passes/mod.rs`, add alongside the other `pub mod` lines:

```rust
pub mod warnings;
```

- [ ] **Step 3: Add the fields to `ModuleCheckResult`**

In `src/typecheck_db/driver_multi.rs`, inside `pub struct ModuleCheckResult` (`:53`), add after `cached: bool` (adjust trailing comma placement):

```rust
    /// IDE span→type map for hover. Populated only when inference runs with
    /// recording enabled (LSP path). Transient; never cached.
    pub span_types: std::collections::HashMap<crate::span::Span, crate::typecheck_db::types::Type>,
    /// Non-fatal warnings (unused imports / bindings). Transient; not an
    /// error channel — see `has_errors`.
    pub warnings: Vec<crate::typecheck_db::passes::warnings::Warning>,
```

- [ ] **Step 4: Update both constructors**

In `from_memo` (`:110`) add `span_types: HashMap::new(), warnings: Vec::new(),` to the struct literal. In the main constructor (`:3354`) add the same two fields. Do **not** add them to `has_errors` (`:133`) — warnings are not errors.

- [ ] **Step 5: Build**

Run: `cargo build --lib`
Expected: compiles (the two new fields are empty everywhere for now).

- [ ] **Step 6: Run the lib suite**

Run: `cargo test --lib typecheck_db 2>&1 | tail -15`
Expected: same pass/fail counts as before this task (no regressions).

- [ ] **Step 7: Commit**

```bash
git add src/typecheck_db/passes/warnings.rs src/typecheck_db/passes/mod.rs src/typecheck_db/driver_multi.rs
git commit -m "typecheck_db: add span_types + warnings fields to ModuleCheckResult"
```

---

### Task A2: Span→type recording in inference

Record each expression/binder/record-label span → inferred type, mirroring the existing `pending_exhaust` sidecar on `UnifyState`.

**Files:**
- Modify: `src/typecheck_db/unify.rs:234` (struct + methods), `src/typecheck_db/passes/infer_value.rs` (`infer_expr:364`, `infer_record:2714`, `infer_record_access:2756`, drain in `infer_value_scc_with_all:968` near `:1354`), `src/typecheck_db/driver_multi.rs` (populate `span_types` from the SCC result)
- Test: `src/typecheck_db/tests/ide.rs` (new), `src/typecheck_db/tests/mod.rs`

**Interfaces:**
- Consumes: `ModuleCheckResult.span_types` (Task A1).
- Produces: `UnifyState::record_span_type(Span, Type)`, `UnifyState::take_span_types() -> HashMap<Span, Type>`, recording enabled by default (a `bool`/`Option` toggle on `UnifyState`).

- [ ] **Step 1: Register the test module**

In `src/typecheck_db/tests/mod.rs` add:

```rust
mod ide;
```

- [ ] **Step 2: Write the failing test**

Create `src/typecheck_db/tests/ide.rs` with the shared helpers (from "Test harness reference" above) plus:

```rust
#[test]
fn span_types_record_local_variable_type() {
    // `x` is a lambda parameter used in the body; hovering it should be Int.
    let src = "module Test where\n\nfoo :: Int -> Int\nfoo = \\x -> x + 1\n";
    let r = check_one("Test", src);
    // The `x` in `x + 1` (its use site) must have a recorded Int type.
    let use_off = offset_of(src, "x + 1");
    let found = r.span_types.iter().find(|(s, _)| use_off >= s.start && use_off < s.end);
    let (_, ty) = found.expect("a span covering the use of `x` should be recorded");
    assert_eq!(ty.to_string(), "Int", "recorded type for `x`: {ty}");
}

#[test]
fn span_types_record_top_level_body_type() {
    let src = "module Test where\n\nfoo = 42\n";
    let r = check_one("Test", src);
    let off = offset_of(src, "42");
    let found = r.span_types.iter().find(|(s, _)| off >= s.start && off < s.end);
    assert_eq!(found.expect("literal span recorded").1.to_string(), "Int");
}
```

- [ ] **Step 3: Run to verify failure**

Run: `cargo test --lib typecheck_db::tests::ide::span_types -- --nocapture 2>&1 | tail -20`
Expected: FAIL — `span_types` is empty (no recording yet).

- [ ] **Step 4: Add the sidecar to `UnifyState`**

In `src/typecheck_db/unify.rs`, inside `pub struct UnifyState` (`:234`), add a field next to `pending_exhaust`:

```rust
    // IDE span→type recording. Populated by `infer_expr` when
    // `record_spans` is true; drained by the SCC driver via
    // `take_span_types`. Mirrors the `pending_exhaust` sidecar.
    span_types: std::collections::HashMap<crate::span::Span, Type>,
    record_spans: bool,
```

In `UnifyState::new()` initialise `span_types: std::collections::HashMap::new(), record_spans: true,` (always-on per Global Constraints). Add methods on the `impl UnifyState`:

```rust
    pub fn set_record_spans(&mut self, on: bool) { self.record_spans = on; }
    pub fn record_span_type(&mut self, span: crate::span::Span, ty: Type) {
        if self.record_spans {
            self.span_types.insert(span, ty);
        }
    }
    pub fn take_span_types(&mut self) -> std::collections::HashMap<crate::span::Span, Type> {
        std::mem::take(&mut self.span_types)
    }
```

- [ ] **Step 5: Record in `infer_expr`**

In `src/typecheck_db/passes/infer_value.rs`, in `infer_expr` (`:364`), after `let result = infer_expr_inner(...)` and before restoring the unify span, record on success:

```rust
    let result = infer_expr_inner(state, env, type_ops, expr);
    if let Ok(ty) = &result {
        let sp = expr.span();
        state.record_span_type(sp, ty.clone());
    }
    state.set_current_unify_span(prev_unify_span);
    result
```

Additionally, in `infer_record` (`:2714`) record each field-value expression's span→type (it already infers them), and in `infer_record_access` (`:2756`) record the accessed field's result type at the access span, so record-label hovers resolve. Use `state.record_span_type(field_span, field_ty.clone())` at each site (read the two functions to find the field/label spans).

- [ ] **Step 6: Zonk + drain in the SCC driver**

In `infer_value_scc_with_all` (`:968`), near where `state.take_pending_exhaust()` is drained (`:1354`), after the SCC's final substitution is available, drain and zonk:

```rust
    let mut span_types = state.take_span_types();
    for ty in span_types.values_mut() {
        *ty = state.zonk(ty);   // use the same zonk entry point the schemes use
    }
```

Return `span_types` from `infer_value_scc_with_all` (extend its return tuple/struct) so `check_one_module` can aggregate it. Read the function's current return shape and thread one extra value; update `infer_value_scc_with_registries` (`:951`) if it shares the return type.

- [ ] **Step 7: Aggregate into `ModuleCheckResult`**

In `check_one_module` (`driver_multi.rs:1005`), accumulate a module-level `span_types` map across SCCs from the value returned in Step 6, and set it on the final `ModuleCheckResult` (`:3354`) instead of the empty map.

- [ ] **Step 8: Run the test**

Run: `cargo test --lib typecheck_db::tests::ide::span_types -- --nocapture 2>&1 | tail -20`
Expected: PASS.

- [ ] **Step 9: Full lib suite (no regressions)**

Run: `cargo test --lib typecheck_db 2>&1 | tail -15`
Expected: no new failures.

- [ ] **Step 10: Commit**

```bash
git add src/typecheck_db/unify.rs src/typecheck_db/passes/infer_value.rs src/typecheck_db/driver_multi.rs src/typecheck_db/tests/
git commit -m "typecheck_db: record span->type map during inference (hover support)"
```

---

### Task A3: Unused-import / unused-name warnings

Track referenced names during checking; diff against imported names and local bindings; emit warnings. Ports the old typechecker mechanism (`src/typechecker/check/mod.rs:9393`).

**Files:**
- Modify: `src/typecheck_db/passes/warnings.rs` (add the diff fn), `src/typecheck_db/passes/imports.rs` (expose imported-name spans), `src/typecheck_db/unify.rs` or the inference context (track referenced names), `src/typecheck_db/passes/infer_value.rs` (record refs in `infer_var`/constructor), the type-conversion path (record type/class refs), `src/typecheck_db/driver_multi.rs` (`check_one_module` — run the diff, populate `warnings`)
- Test: `src/typecheck_db/tests/ide.rs`

**Interfaces:**
- Consumes: `ModuleCheckResult.warnings` (A1), `Warning`/`WarningKind` (A1).
- Produces: `warnings::compute_unused(imported: &[(String, Span)], referenced: &std::collections::HashSet<String>) -> Vec<Warning>`.

- [ ] **Step 1: Write the failing tests**

Append to `src/typecheck_db/tests/ide.rs`:

```rust
use crate::typecheck_db::passes::warnings::WarningKind;

#[test]
fn unused_import_is_warned() {
    let lib = "module Lib where\n\nused :: Int\nused = 1\n\nunused :: Int\nunused = 2\n";
    let main = "module Main where\nimport Lib (used, unused)\nmain :: Int\nmain = used\n";
    let module = crate::parser::parse(main).expect("parse main");
    let libm = crate::parser::parse(lib).expect("parse lib");
    let report = check_many_modules(vec![
        ModuleInput::new("Lib", lib, libm),
        ModuleInput::new("Main", main, module),
    ]);
    let main_r = report.results.iter().find(|r| r.name == "Main").unwrap();
    let unused: Vec<_> = main_r.warnings.iter()
        .filter_map(|w| match &w.kind { WarningKind::UnusedImport { name } => Some(name.clone()), _ => None })
        .collect();
    assert!(unused.contains(&"unused".to_string()), "should warn `unused`: {unused:?}");
    assert!(!unused.contains(&"used".to_string()), "must NOT warn `used`: {unused:?}");
}

#[test]
fn type_only_used_in_signature_is_not_unused() {
    // `Lib.T` is referenced only in a signature — must not be flagged unused.
    let lib = "module Lib where\n\ndata T = T\n";
    let main = "module Main where\nimport Lib (T(..))\nmk :: T\nmk = T\n";
    let libm = crate::parser::parse(lib).expect("parse lib");
    let mainm = crate::parser::parse(main).expect("parse main");
    let report = check_many_modules(vec![
        ModuleInput::new("Lib", lib, libm),
        ModuleInput::new("Main", main, mainm),
    ]);
    let main_r = report.results.iter().find(|r| r.name == "Main").unwrap();
    let unused: Vec<_> = main_r.warnings.iter()
        .filter_map(|w| match &w.kind { WarningKind::UnusedImport { name } => Some(name.clone()), _ => None })
        .collect();
    assert!(unused.is_empty(), "type used in signature is not unused: {unused:?}");
}
```

- [ ] **Step 2: Run to verify failure**

Run: `cargo test --lib typecheck_db::tests::ide::unused -- --nocapture 2>&1 | tail -20; cargo test --lib typecheck_db::tests::ide::type_only -- --nocapture 2>&1 | tail -20`
Expected: FAIL — `warnings` empty.

- [ ] **Step 3: Add the diff function**

In `src/typecheck_db/passes/warnings.rs`:

```rust
use std::collections::HashSet;

/// Emit `UnusedImport` for every imported name absent from `referenced`.
/// Names beginning with `_` are exempt (intentional-unused convention).
pub fn compute_unused_imports(
    imported: &[(String, Span)],
    referenced: &HashSet<String>,
) -> Vec<Warning> {
    let mut seen: HashSet<(&str, usize)> = HashSet::new();
    let mut out = Vec::new();
    for (name, span) in imported {
        if name.starts_with('_') || name.is_empty() { continue; }
        if referenced.contains(name) { continue; }
        if !seen.insert((name.as_str(), span.start)) { continue; }
        out.push(Warning { span: *span, kind: WarningKind::UnusedImport { name: name.clone() } });
    }
    out
}
```

- [ ] **Step 4: Track referenced names**

Add a `referenced_names: HashSet<String>` sidecar to `UnifyState` (or the inference context), with `record_reference(name)` / `take_references()` methods, mirroring `span_types` (Task A2 Step 4). Record a reference in `infer_var` (value/qualified refs) and in constructor inference (`infer_constructor`), storing both qualified and unqualified forms (the old code notes this at `check/mod.rs:9414`). In the type-conversion path (`convert_type_expr` and wherever class constraints are converted), record type-constructor and class references too. Read `infer_var` first to find the resolved-name string.

- [ ] **Step 5: Expose imported-name spans**

In `src/typecheck_db/passes/imports.rs`, add a way to return the list of `(imported_name, span)` bound by the module's explicit import lists (the resolver already walks `cst::ImportList`). Return unqualified names for explicit imports; skip open imports (`import M` with no list) since the old compiler does not report those as removable. Expose it so `check_one_module` can call it.

- [ ] **Step 6: Run the diff in `check_one_module`**

After inference finishes in `check_one_module` (`driver_multi.rs`), gather `referenced = state.take_references()` (threaded out of the SCC driver like `span_types`), collect the imported-name spans (Step 5), call `warnings::compute_unused_imports`, and set the result on `ModuleCheckResult.warnings` (`:3354`).

- [ ] **Step 7: Run the tests**

Run: `cargo test --lib typecheck_db::tests::ide -- --nocapture 2>&1 | tail -25`
Expected: PASS (A2 + A3 tests).

- [ ] **Step 8: Full lib suite**

Run: `cargo test --lib typecheck_db 2>&1 | tail -15`
Expected: no new failures. (Warnings are not errors; `has_errors` unaffected; memoization unchanged.)

- [ ] **Step 9: Commit**

```bash
git add src/typecheck_db/
git commit -m "typecheck_db: unused-import warnings (reference tracking + diff)"
```

---

### Task A4: Surface kinds on exports for hover

Give hover a renderable kind per exported type constructor and class.

**Files:**
- Modify: `src/typecheck_db/passes/instance_index.rs:64` (`ClassInfo`), `src/typecheck_db/module_registry.rs` (carry kind on exports; kind computed near `:451`)
- Test: `src/typecheck_db/tests/ide.rs`

**Interfaces:**
- Produces: a renderable kind string reachable from `ModuleExports` for (a) each class and (b) each type constructor. Concretely: `ClassInfo` gains `pub param_kinds: Vec<crate::typecheck_db::types::Type>` (kind per class type var, defaulting to `Type`), and `ModuleExports` gains `pub type_kinds: HashMap<String, crate::typecheck_db::types::Type>` (full kind per exported type/class name, e.g. `Type -> Constraint`).

- [ ] **Step 1: Write the failing test**

Append to `src/typecheck_db/tests/ide.rs`:

```rust
#[test]
fn exports_carry_class_and_type_kinds() {
    let src = "module Test where\n\nclass MyShow a where\n  myShow :: a -> String\n\ndata Box a = MkBox a\n";
    let r = check_one("Test", src);
    let report = {
        let module = crate::parser::parse(src).unwrap();
        check_many_modules(vec![ModuleInput::new("Test", src, module)])
    };
    let exports = report.registry.get("Test").expect("Test exports");
    let _ = r;
    assert_eq!(exports.type_kinds.get("MyShow").map(|k| k.to_string()), Some("Type -> Constraint".to_string()));
    assert_eq!(exports.type_kinds.get("Box").map(|k| k.to_string()), Some("Type -> Type".to_string()));
}
```

- [ ] **Step 2: Run to verify failure**

Run: `cargo test --lib typecheck_db::tests::ide::exports_carry -- --nocapture 2>&1 | tail -20`
Expected: FAIL — `type_kinds` field does not exist / is empty.

- [ ] **Step 3: Add the fields**

In `instance_index.rs` (`:64`) add `pub param_kinds: Vec<crate::typecheck_db::types::Type>` to `ClassInfo` (default all-`Type` where unknown). In `module_registry.rs`, add `pub type_kinds: std::collections::HashMap<String, crate::typecheck_db::types::Type>` to `ModuleExports` and initialise it empty in every `ModuleExports` constructor/`Default`.

- [ ] **Step 4: Populate the kinds**

Where `ModuleExports` is built for a module (around the class/type export construction; `class_var_kinds` is already computed near `module_registry.rs:451`), build each type/class's full kind as a right-associated arrow chain: for a class, `param_kinds.iter().rev().fold(prim_constraint(), |acc, k| Fun(k, acc))`; for a data/newtype/foreign type, use its arity (`type_arities`) with each param defaulting to `Type` → `Fun(Type, … Fun(Type, Type))`. Use the actual param kinds from the kind pass (`class_var_kinds`, `kind_check::ParamKind`) where available so higher-kinded params (`(Type -> Type) -> Constraint`) render correctly. Insert into `type_kinds`.

- [ ] **Step 5: Run the test**

Run: `cargo test --lib typecheck_db::tests::ide::exports_carry -- --nocapture 2>&1 | tail -20`
Expected: PASS.

- [ ] **Step 6: Verify higher-kinded rendering (fixture parity)**

Add and run:

```rust
#[test]
fn exports_carry_higher_kinded_class_kind() {
    let src = "module Test where\n\nclass MyFunctor f where\n  mmap :: forall a b. (a -> b) -> f a -> f b\n";
    let module = crate::parser::parse(src).unwrap();
    let report = check_many_modules(vec![ModuleInput::new("Test", src, module)]);
    let exports = report.registry.get("Test").unwrap();
    assert_eq!(exports.type_kinds.get("MyFunctor").map(|k| k.to_string()),
        Some("(Type -> Type) -> Constraint".to_string()));
}
```

Run: `cargo test --lib typecheck_db::tests::ide::exports_carry_higher -- --nocapture 2>&1 | tail -20`
Expected: PASS. If FAIL (param kind not inferred), enrich the kind pass to fill `param_kinds` from method-signature usage; this is the flagged A3-risk item.

- [ ] **Step 7: Full lib suite**

Run: `cargo test --lib typecheck_db 2>&1 | tail -15`
Expected: no new failures.

- [ ] **Step 8: Commit**

```bash
git add src/typecheck_db/
git commit -m "typecheck_db: surface renderable type/class kinds on ModuleExports"
```

---

## Phase B — Single-module IDE entry point

### Task B1: `check_module_ide`

**Files:**
- Modify: `src/typecheck_db/driver_multi.rs` (add `pub fn check_module_ide` near `:194`; ensure `check_one_module` can force full re-inference)
- Test: `src/typecheck_db/tests/ide.rs`

**Interfaces:**
- Consumes: `check_one_module` (`:1005`), `ModuleRegistry`, `ModuleInput`.
- Produces: `pub fn check_module_ide(db: &mut TypecheckDb, input: &ModuleInput, registry: &ModuleRegistry) -> ModuleCheckResult`.

- [ ] **Step 1: Write the failing test**

Append to `src/typecheck_db/tests/ide.rs`:

```rust
use crate::typecheck_db::driver::TypecheckDb;
use crate::typecheck_db::driver_multi::check_module_ide;

#[test]
fn check_module_ide_gives_complete_span_types_against_warm_registry() {
    // Warm the registry with Lib, then IDE-check Main; span_types must cover
    // Main's locals even though Main has two decls (one unedited-looking).
    let lib = "module Lib where\n\nbase :: Int\nbase = 1\n";
    let main = "module Main where\nimport Lib (base)\n\nfirst :: Int\nfirst = base\n\nsecond :: Int -> Int\nsecond = \\y -> y + base\n";
    let mut db = TypecheckDb::open_in_memory().unwrap();
    let libm = crate::parser::parse(lib).unwrap();
    let mainm = crate::parser::parse(main).unwrap();
    // Populate the registry via a normal multi-check.
    let report = crate::typecheck_db::driver_multi::check_many_modules_with_db(
        &mut db, vec![ModuleInput::new("Lib", lib, libm), ModuleInput::new("Main", main, mainm.clone())]);
    let registry = report.registry;
    // Now IDE-check Main against the warm registry.
    let input = ModuleInput::new("Main", main, mainm);
    let r = check_module_ide(&mut db, &input, &registry);
    let off = offset_of(main, "y + base");
    let found = r.span_types.iter().find(|(s, _)| off >= s.start && off < s.end);
    assert!(found.is_some(), "IDE check must record span types for Main's locals");
    assert!(r.import_errors.is_empty(), "warm registry resolves `base`: {:?}", r.import_errors);
}
```

- [ ] **Step 2: Run to verify failure**

Run: `cargo test --lib typecheck_db::tests::ide::check_module_ide -- --nocapture 2>&1 | tail -20`
Expected: FAIL — `check_module_ide` undefined.

- [ ] **Step 3: Implement `check_module_ide`**

In `driver_multi.rs`, add:

```rust
/// Check ONE module against an already-populated (warm) `registry`, forcing
/// full re-inference so `span_types` and `warnings` are complete across the
/// whole module (not just changed decls). The LSP entry point. Does not
/// mutate the shared plan state beyond what a normal single-module check does.
pub fn check_module_ide(
    db: &mut TypecheckDb,
    input: &ModuleInput,
    registry: &ModuleRegistry,
) -> ModuleCheckResult {
    let mut reg = registry.clone();
    // imports_iface_hash = 0: IDE checks don't participate in the cross-build
    // drift key; full re-inference is forced regardless.
    check_one_module(db, input, &mut reg, [0u8; 32])
}
```

Then ensure `check_one_module` re-infers the focused module fully. If per-decl cache hits would skip inference, add a `force_full: bool` parameter (or an `ide` flag) threaded from `check_module_ide` into the SCC loop so `try_get_cached` is bypassed for this module. Read the caching branch in `check_one_module` (around the `infer_value_scc_with_all` call at `:2117`) to place the bypass. Keep the default (`check_many_modules_with_db`) path unchanged.

- [ ] **Step 4: Run the test**

Run: `cargo test --lib typecheck_db::tests::ide::check_module_ide -- --nocapture 2>&1 | tail -20`
Expected: PASS.

- [ ] **Step 5: Full lib suite**

Run: `cargo test --lib typecheck_db 2>&1 | tail -15`
Expected: no new failures.

- [ ] **Step 6: Commit**

```bash
git add src/typecheck_db/
git commit -m "typecheck_db: add check_module_ide single-module IDE entry point"
```

---

## Phase C — Rewire the LSP

> From here, `cargo test --test lsp_e2e` is the guardrail. Run it after each task. Tasks are ordered so the crate keeps compiling; intermediate tasks may adapt a handler while a sibling still uses the old path until its own task lands. If a whole-crate build is briefly red between sub-steps, that's expected — each task ends green.

### Task C1: Backend state swap

**Files:**
- Modify: `src/lsp/mod.rs:16-98` (imports, `Backend` struct, `new_with_options`)

**Interfaces:**
- Produces: `Backend.registry: Arc<RwLock<crate::typecheck_db::module_registry::ModuleRegistry>>`; `Backend.db: Arc<tokio::sync::Mutex<crate::typecheck_db::driver::TypecheckDb>>`.

- [ ] **Step 1: Swap the registry + cache types**

In `src/lsp/mod.rs`:
- Replace `use crate::typechecker::registry::ModuleRegistry;` (`:18`) with `use crate::typecheck_db::module_registry::ModuleRegistry;`.
- Replace `use crate::build::cache::ModuleCache;` (`:16`) — remove it.
- In `struct Backend` replace `pub(crate) module_cache: Arc<RwLock<ModuleCache>>,` (`:91`) with:

```rust
    pub(crate) db: Arc<tokio::sync::Mutex<crate::typecheck_db::driver::TypecheckDb>>,
```

- [ ] **Step 2: Initialise in `new_with_options`**

In `new_with_options` (`:322`) replace the `module_cache: …` initialiser with a `TypecheckDb` opened at the cache/output location (persistent if a path is available, else in-memory):

```rust
    db: Arc::new(tokio::sync::Mutex::new({
        let mut db = match &output_dir {
            Some(dir) => crate::typecheck_db::driver::TypecheckDb::open(&dir.join(".pfc-decldb.sqlite"))
                .unwrap_or_else(|_| crate::typecheck_db::driver::TypecheckDb::open_in_memory().expect("in-memory db")),
            None => crate::typecheck_db::driver::TypecheckDb::open_in_memory().expect("in-memory db"),
        };
        db.set_codegen(output_dir.is_some());
        db.set_output_dir(output_dir.clone());
        db
    })),
```

(Confirm `TypecheckDb::open`'s exact signature in `driver.rs`; adjust the path handling to match how `run_compile_db` opens it in `main.rs:169-176`.)

- [ ] **Step 3: Build (expect handler errors)**

Run: `cargo build --lib 2>&1 | grep -E "error" | head -30`
Expected: errors only in handler files that still reference the old registry/cache (fixed in later tasks). `mod.rs` itself compiles.

- [ ] **Step 4: Commit**

```bash
git add src/lsp/mod.rs
git commit -m "lsp: swap Backend to typecheck_db registry + TypecheckDb (state only)"
```

### Task C2: Resolution / Prim (`utils/resolve.rs`)

**Files:**
- Modify: `src/lsp/utils/resolve.rs:14,74,259-266,359-384,541,595,607-610,881`

**Interfaces:**
- Consumes: `crate::typecheck_db::prim::prim_exports()`, `crate::typecheck_db::module_registry::ModuleExports`.
- Produces: `module_exports_to_resolved_names(&typecheck_db ModuleExports) -> ModuleResolvedNames` (same return type as today).

- [ ] **Step 1: Replace prim calls**

Replace `crate::typechecker::check::prim_exports()` and `prim_submodule_exports(name)` (`:74,259,261,266,595,607-610,881`) with lookups into `crate::typecheck_db::prim::prim_exports()` (a `HashMap<String, ModuleExports>` covering `Prim` and `Prim.*`). Remove `use crate::typechecker::error::TypeError;` (`:14`) if now unused (or swap to the typecheck_db error import if referenced).

- [ ] **Step 2: Rewrite the exports→resolved-names conversion**

Rewrite `module_exports_to_resolved_names` (`:359`) to read the typecheck_db `ModuleExports` shape: `values` (keys are plain `String`), `ctors` / `data_constructors`, `classes`, `type_aliases`, and the `*_origins` maps. Map each into the existing `ModuleResolvedNames` structure (keep its field layout; only the source changes). Do the same for the other conversion site (`:541`).

- [ ] **Step 3: Build resolve.rs**

Run: `cargo build --lib 2>&1 | grep -E "resolve.rs" | head -20`
Expected: no errors originating in `resolve.rs`.

- [ ] **Step 4: Commit**

```bash
git add src/lsp/utils/resolve.rs
git commit -m "lsp: resolution + prim scopes from typecheck_db exports"
```

### Task C3: Project load (`handlers/load_sources.rs`)

**Files:**
- Modify: `src/lsp/handlers/load_sources.rs:17,522-530,730-745,737` and the cold-build path

**Interfaces:**
- Consumes: `Backend.db`, `Backend.registry` (typecheck_db), `check_many_modules_with_db`.
- Produces: populated `registry`, `def_index`, `completion_index`, `resolution_exports`.

- [ ] **Step 1: Replace the incremental build**

Replace the `use crate::typechecker::registry::ModuleRegistry;` (`:17`) with the typecheck_db one. Replace the cold-build call to `build::build_from_sources_incremental` + `ModuleCache` with a persistent `TypecheckDb` build: parse all discovered sources into `ModuleInput`s and call `check_many_modules_with_db(&mut *db_guard, inputs)` (lock `self.db`), storing `report.registry` into `self.registry`. Populate `resolution_exports` from `report.registry` via the C2 conversion.

- [ ] **Step 2: Replace open-file typecheck**

Replace `crate::typechecker::check_module_with_registry(&module, &reg)` (`:737`) with `check_module_ide(&mut *db_guard, &input, &registry)`; keep the diagnostics publication.

- [ ] **Step 3: Build**

Run: `cargo build --lib 2>&1 | grep -E "load_sources.rs" | head -20`
Expected: no errors in `load_sources.rs`.

- [ ] **Step 4: Commit**

```bash
git add src/lsp/handlers/load_sources.rs
git commit -m "lsp: project load via persistent TypecheckDb"
```

### Task C4: Diagnostics (`handlers/diagnostics.rs`)

**Files:**
- Modify: `src/lsp/handlers/diagnostics.rs:8,34,104,117,202-233`

**Interfaces:**
- Consumes: `check_module_ide`, `ModuleCheckResult`, `warnings::Warning`.
- Produces: `to_diagnostics(&ModuleCheckResult, source: &str) -> Vec<Diagnostic>`.

- [ ] **Step 1: Replace the check call**

Replace `crate::typechecker::check_module_with_registry(&module, &registry)` (`:104`) with `check_module_ide(&mut *self.db.lock().await, &input, &registry)`. Replace the `module_cache` lazy-import + update logic (`:34,117`) with the registry/db path (deps already live in the registry after load).

- [ ] **Step 2: New diagnostics mapping**

Replace `type_errors_to_diagnostics` / `type_warnings_to_diagnostics` (`:202,232`) with a single `to_diagnostics(result, source)` that walks each error channel — `import_errors`, `validation_errors`, `kind_errors`, `coercible_errors`, `exhaustiveness_errors`, `constraint_errors`, `inference_error`, `hole_diagnostics` — plus `warnings` (severity `WARNING`, plus a `diagnostic.code = "UnusedImport"` so code actions can find them). Each carries a `crate::span::Span`; reuse the existing span→`Range` conversion helper in this file. Give each a readable `message` (Display the underlying error/type).

- [ ] **Step 2b: Write a smoke test**

The e2e suite covers this end-to-end; add one focused check to `tests/lsp_e2e.rs` mirroring an existing diagnostics test if none asserts an error squiggle. (If an existing test already covers a type error, skip.)

- [ ] **Step 3: e2e**

Run: `cargo test --test lsp_e2e 2>&1 | tail -20`
Expected: initialize/diagnostics-related tests pass; hover/code-action tests may still fail until C5/C6.

- [ ] **Step 4: Commit**

```bash
git add src/lsp/handlers/diagnostics.rs tests/lsp_e2e.rs
git commit -m "lsp: diagnostics via check_module_ide + typecheck_db error/warning mapping"
```

### Task C5: Hover (`handlers/hover.rs`)

**Files:**
- Modify: `src/lsp/handlers/hover.rs:11-12,15,221,242,248,428`

**Interfaces:**
- Consumes: `check_module_ide().span_types`, registry `ModuleExports.values` (`Scheme`/`Type` `Display`), `ModuleExports.type_kinds` (A4).

- [ ] **Step 1: Replace the type formatter**

Replace `use crate::typechecker::error::pretty_type;` and `fn fmt_ty` (`:11-15`) with rendering via `typecheck_db` `Type`/`Scheme` `Display` (`ty.to_string()`). Replace `use crate::typechecker::types::Type;` (`:12`) with the typecheck_db `Type`.

- [ ] **Step 2: Span + local hover from `span_types`**

In `hover_span_type` (`:221`) and `get_local_var_type` (`:242`), replace `check_module_for_ide(...)` with `check_module_ide(&mut *self.db.lock().await, &input, &registry)` and read `.span_types` (offset-in-span lookup as today).

- [ ] **Step 3: Decl + kind hover from the registry**

In `get_local_type` (`:248`) read the decl's scheme from `registry.get(module)?.values.get(name)` and `Display` it; fall back to CST signatures as today. Replace the kind extraction (`:428`) with `registry.get(module)?.type_kinds.get(name)` (A4).

- [ ] **Step 4: Doc comments**

Confirm where hover docs come from today (module_doc vs CST comments). If from old-exports `module_doc`, source the docs from CST comment nodes instead (the LSP already parses CST); the hover fixture asserts `doc:` substrings, so keep them working.

- [ ] **Step 5: e2e hover**

Run: `cargo test --test lsp_e2e hover 2>&1 | tail -25`
Expected: all `test_lsp_hover_*` including `test_lsp_hover_fixture` pass.

- [ ] **Step 6: Commit**

```bash
git add src/lsp/handlers/hover.rs
git commit -m "lsp: hover via typecheck_db span_types + registry schemes + kinds"
```

### Task C6: Code actions (`handlers/code_action.rs`)

**Files:**
- Modify: `src/lsp/handlers/code_action.rs:76,81-82`

- [ ] **Step 1: Unused imports from warnings**

Replace `crate::typechecker::check_module_with_registry(module, &registry)` (`:76`) with `check_module_ide(...)`, and the `TypeWarning::UnusedImport { span, .. }` filter (`:82`) with `warnings::WarningKind::UnusedImport { .. }` over `result.warnings`.

- [ ] **Step 2: e2e code actions**

Run: `cargo test --test lsp_e2e code_action 2>&1 | tail -25`
Expected: all `test_lsp_code_action_*` pass.

- [ ] **Step 3: Commit**

```bash
git add src/lsp/handlers/code_action.rs
git commit -m "lsp: unused-import code actions via typecheck_db warnings"
```

### Task C7: Cleanup + full green

**Files:**
- Modify: any remaining `src/lsp/**` files with `crate::typechecker` references

- [ ] **Step 1: Find remaining references**

Run: `grep -rn "crate::typechecker" src/lsp/`
Expected: eventually **empty**. Fix each remaining site (types/imports) to the typecheck_db equivalent.

- [ ] **Step 2: Whole crate builds clean**

Run: `cargo build 2>&1 | tail -15`
Expected: builds; no errors. (Warnings about now-unused old-typechecker items outside the LSP are acceptable.)

- [ ] **Step 3: Full e2e suite**

Run: `cargo test --test lsp_e2e 2>&1 | tail -20`
Expected: all 31 tests pass.

- [ ] **Step 4: Full test suite (no regressions elsewhere)**

Run: `cargo test 2>&1 | tail -30`
Expected: no new failures vs. the pre-migration baseline.

- [ ] **Step 5: Manual smoke (optional but recommended)**

Build the server and open the oa app in an editor (or run an LSP client script) to confirm hover/diagnostics/completion/goto/code-actions behave; check per-edit latency is acceptable.

- [ ] **Step 6: Commit**

```bash
git add src/lsp/
git commit -m "lsp: remove all crate::typechecker references (migration complete)"
```

---

## Self-Review

**Spec coverage:**
- Span→type recording → A1/A2/B1. ✓
- Unused-import/name warnings → A1/A3, consumed in C4/C6. ✓
- Surface kinds for hover → A4, consumed in C5. ✓
- Single-module IDE entry point → B1, consumed in C3/C4/C5/C6. ✓
- Backend state (registry + db) → C1. ✓
- Project load via persistent TypecheckDb → C3. ✓
- Diagnostics mapping (8 channels + warnings) → C4. ✓
- Hover (span + decl + kinds + docs) → C5. ✓
- Code actions (unused imports) → C6. ✓
- Resolution/prim rewrite → C2. ✓
- Remove all `crate::typechecker` from LSP → C7. ✓
- Always-on + transient semantics → Global Constraints + A2 (`record_spans`) + B1 (force full re-inference). ✓
- Leave `crate::typechecker` in place → Global Constraints + C7 note. ✓

**Type consistency:** `check_module_ide(db, input, registry) -> ModuleCheckResult` used identically in C3/C4/C5/C6. `span_types`/`warnings` field names consistent A1↔A2↔A3↔C. `ModuleExports.type_kinds` consistent A4↔C5. `WarningKind::UnusedImport { name }` consistent A1↔A3↔C6.

**Placeholder scan:** Implementation steps that require reading a specific function before editing (A2 record sites, A3 reference tracking, B1 cache bypass, C2 conversion, C5 docs) name the exact function + anchor line and the precise change; test steps carry full runnable code. No "TBD"/"handle edge cases"/"similar to Task N".

**Known judgement calls left to the implementer (by design, anchored):**
- Exact return-shape threading of `span_types`/`referenced` out of `infer_value_scc_with_all` (A2/A3) — depends on that function's current return tuple; anchored at `:968`/`:1354`.
- Exact `TypecheckDb::open` path handling in C1 — mirror `main.rs:169-176`.
