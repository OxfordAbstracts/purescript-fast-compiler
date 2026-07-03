# Design: Move the LSP fully onto `typecheck_db`

**Date:** 2026-07-03
**Branch:** `typecheck-db`
**Status:** Approved design (pending spec review)

## Goal

Remove every dependency of `src/lsp/` on the old `crate::typechecker` and make the
LSP run entirely on `crate::typecheck_db` (the DeclDb-driven, incremental,
per-declaration engine that already drives `pfc compile-db`). All current LSP
functionality is preserved.

**Non-goal:** deleting `crate::typechecker`. It stays in place for its other
callers (`build::build_cached`, the `compile` command, existing tests). Only the
LSP stops referencing it.

## Acceptance criteria

The regression bar is the existing end-to-end suite, which must stay green:

- `tests/lsp_e2e.rs` — 31 tests: initialize/capabilities, go-to-definition,
  hover, completion (incl. auto-import), formatting, and code actions (remove
  unused imports).
- `tests/fixtures/lsp/hover/Simple.purs` — the fixture-driven hover test asserts
  ~15 positions including **local variables, let/where bindings, case binders,
  record labels, sub-expressions, and kinds** (e.g. `Type -> Constraint`,
  `(Type -> Type) -> Constraint`). This is the concrete target for the two new
  typecheck_db capabilities below.
- New unit tests in `typecheck_db` for span-type recording and unused-import
  analysis (Part A), independent of the LSP.

## Background: current coupling

The LSP depends on the old typechecker in these ways (verified):

| Symbol | Used by | Purpose |
|---|---|---|
| `check_module_with_registry(&Module, &Registry) -> CheckResult` | diagnostics, hover, code_action, load_sources | per-module check → errors, warnings, decl types, exports |
| `check_module_for_ide(...) -> CheckResult` (adds `span_types`) | hover | types for arbitrary spans / locals |
| `prim_exports()`, `prim_submodule_exports(name)` | resolve.rs | Prim + Prim.* name scopes |
| `pretty_type(&Type, &map) -> String` | hover | render a type as a string |
| Types: `registry::{ModuleRegistry, ModuleExports}`, `error::{TypeError, TypeWarning}`, `types::Type` | throughout | state + diagnostic/hover data |
| `build::cache::ModuleCache`, `build::build_from_sources_incremental` | load_sources.rs | project load + incremental cache |

`CheckResult` carries: `types` (top-level decl types), `errors`, `warnings`
(incl. `UnusedImport`/`UnusedName`), `exports`, `span_types` (Span→Type).

## Gaps in `typecheck_db` (must be filled)

`typecheck_db` today produces, per module, a `ModuleCheckResult` with eight error
channels (import, validation, kind, coercible, constraint, exhaustiveness,
inference, holes) — richer than the old `TypeError` set — plus top-level
`InferredScheme`s and (optionally) generated JS. It does **not** have:

1. **A span→type map** (`span_types`). Only top-level `InferredScheme`s exist.
2. **A warning channel.** No `UnusedImport`/`UnusedName`; no `warnings` field.
3. **Renderable kinds surfaced through exports.** Kinds *are* computed
   (`kind_check::ParamKind`, `class_var_kinds` at `module_registry.rs:451`) but
   are not exposed on `ModuleExports` for the LSP to render on hover.

## Decisions (confirmed)

- **Always on** — span-types and warnings are produced whenever a module's
  inference actually runs, not gated behind a special IDE flag. See "Always-on
  semantics" for the cache interaction this implies.
- **Leave `crate::typechecker` in place** — LSP-only migration.
- **Spec → plan → implement**, checking in at phase boundaries (A, B, C).

## Design

The work is three parts: **A** grows `typecheck_db` (independently testable, no
LSP), **B** adds one entry point, **C** rewires the LSP feature-by-feature.

### Part A — Grow `typecheck_db`

#### A1. Span→type recording

- `infer_expr` (`passes/infer_value.rs:364`) is the single choke point for every
  expression, and every `Expr` exposes `.span()`.
- Add `ide_span_types: Option<HashMap<Span, Type>>` to `UnifyState`. When
  `Some`, `infer_expr` inserts `expr.span() → ty` after `infer_expr_inner`
  succeeds. Add explicit inserts at record-label sites (`infer_record`,
  `infer_record_access`) and binder sites (lambda/case/let binder inference), so
  the fixture's local-variable, record-label, and case-binder hovers resolve.
- Zonk the whole map once at the end of the module's SCC inference (types carry
  unification variables until then).
- Surface the finished map as `span_types: HashMap<Span, Type>` on
  `ModuleCheckResult`.
- Per the "always on" decision the recorder is enabled by default whenever
  inference runs. The `Option` is the opt-out lever: setting it to `None` makes
  recording zero-cost, which is how the CLI-overhead follow-up (see below) would
  disable it for non-LSP builds if needed.

#### A2. Unused-import / unused-name warnings

- Add a warning type and channel to `typecheck_db`:
  `warnings: Vec<Warning>` on `ModuleCheckResult`, with
  `Warning { span, kind }` where `kind ∈ { UnusedImport{name}, UnusedName{name} }`.
- Port the old typechecker's proven mechanism (`check/mod.rs:9393`):
  - Track *referenced* names during checking: value/constructor references in
    `infer_var` + constructor inference, **type/class references in
    `convert_type_expr`** (so a type imported only for use in a signature is not
    falsely reported unused), and operator references.
  - Collect the imported-name → span set during import resolution
    (`passes/imports.rs`).
  - At module end, diff imported names against the referenced set; emit
    `UnusedImport` for the remainder. Exempt names beginning with `_`.
  - `UnusedName` (unused let/lambda bindings) mirrors the same diff over local
    bindings.

#### A3. Surface kinds for hover

- Extend `ClassInfo` (`passes/instance_index.rs:64`) and the exported type
  metadata with a renderable kind per type constructor and per class parameter,
  populated from the existing kind pass (`kind_check::ParamKind`,
  `class_var_kinds`).
- The LSP renders these directly (e.g. a class with one `Type` param →
  `Type -> Constraint`; a higher-kinded param → `(Type -> Type) -> Constraint`).
- **Risk:** if per-parameter kinds are not fully populated for every case,
  higher-kinded rendering (the `MyFunctor` fixture line) may need extra work in
  the kind pass. Treated as a distinct, verifiable sub-task.

#### Always-on semantics (cache interaction)

Because span-types and warnings are produced only while inference *runs*, and
`typecheck_db` has a per-declaration cache, a **cache-hit decl produces neither**
(its inference is skipped). Implications:

- **LSP:** the focused module must be **fully re-inferred** on each check so
  hover data and warnings are complete across the *whole* module, not just edited
  decls. `check_module_ide` (Part B) forces this by treating the focused module's
  decls as dirty (bypassing per-decl cache reads for that module only). Its
  dependencies stay warm in the registry.
- **CLI (`compile-db`):** cold builds compute warnings/span-types for all
  modules; warm builds compute them only for re-checked modules. `run_compile_db`
  may print the warnings. This matches typical incremental-compiler behaviour.
- **Persistence:** span-types and warnings are **transient** — never written to
  the SQLite cache and never part of cache keys. This avoids cache bloat and
  keeps `input_hash`/`output_hash` semantics unchanged.
- **CLI overhead note:** computing span-types during ordinary (non-LSP) full
  builds is otherwise-unused work. If this proves measurable on the ~7000-module
  build, span-types recording can be made opt-in (an `ide` flag threaded from
  `check_one_module`) without affecting the LSP. Flagged for review.

### Part B — Single-module IDE entry point

Add to `driver_multi.rs`:

```rust
pub fn check_module_ide(
    db: &mut TypecheckDb,
    input: &ModuleInput,
    registry: &ModuleRegistry,
) -> ModuleCheckResult
```

A thin wrapper over the existing internal `check_one_module`
(`driver_multi.rs:1005`) that:

- runs the focused module against an already-populated (warm) `registry`,
- forces full re-inference of the focused module (per "Always-on semantics"),
- enables span-type recording, and
- returns the `ModuleCheckResult` (all error channels + `span_types` +
  `warnings`).

This is the direct analog of the old `check_module_for_ide` /
`check_module_with_registry`, so the LSP handler structure is preserved.

*Considered alternative:* re-run the whole project via
`check_many_modules_with_db` on every edit and read the focused module's result.
Correct, but O(all modules) per keystroke even with memo restore. The
single-module-against-warm-registry model matches today's latency and is
preferred.

### Part C — Rewire the LSP

#### C1. Backend state (`src/lsp/mod.rs`)

- `registry: Arc<RwLock<typecheck_db::module_registry::ModuleRegistry>>` (swap
  the type).
- Replace `module_cache: Arc<RwLock<build::cache::ModuleCache>>` with
  `db: Arc<tokio::Mutex<TypecheckDb>>` (persistent; opened at the configured
  cache/output path). A `Mutex` (not `RwLock`) because checks need `&mut db` and
  rusqlite's `Connection` is `Send` but `!Sync`.
- `def_index`, `completion_index`, `source_map`, `module_file_map`, `files`
  unchanged in shape.
- `resolution_exports` keeps its type; it is rebuilt from the new exports.

#### C2. Project load (`handlers/load_sources.rs`)

- Replace `build::build_from_sources_incremental` + `ModuleCache` with a
  persistent `TypecheckDb` build (`check_many_modules_with_db`) that populates the
  registry + SQLite cache once at startup / `rebuildProject`.
- Rebuild `def_index` / `completion_index` (already CST-derived) and
  `resolution_exports` (from the checked set) as today; only the
  exports→resolved-names conversion changes shape.

#### C3. Diagnostics (`handlers/diagnostics.rs`)

- Call `check_module_ide` instead of `check_module_with_registry`.
- New mapping from typecheck_db's eight error channels + `warnings` to LSP
  `Diagnostic`s. Every error/warning carries a `Span`; reuse the existing
  span→LSP-range conversion.
- Update `module_cache`-based lazy import loading to the `db`/registry path.

#### C4. Hover (`handlers/hover.rs`)

- `hover_span_type` / `get_local_var_type`: read `check_module_ide().span_types`.
- `get_local_type` (top-level decls): read the registry's
  `ModuleExports.values[name]` and render via `Type`/`Scheme` `Display`
  (replaces `pretty_type`).
- Kinds for types/classes: render from the surfaced kind info (A3).
- Doc comments: confirm the source (exports `module_doc` vs CST comment nodes)
  and keep whichever the LSP already uses; port any `module_doc` read to the new
  exports if present.

#### C5. Code actions (`handlers/code_action.rs`)

- `collect_unused_import_spans`: read `check_module_ide().warnings` filtered to
  `UnusedImport`.

#### C6. Resolution / Prim (`utils/resolve.rs`)

- Replace `prim_exports()` / `prim_submodule_exports()` with
  `typecheck_db::prim::prim_exports()` (a single `HashMap<String, ModuleExports>`
  covering Prim + all submodules).
- Rewrite `module_exports_to_resolved_names` for the new `ModuleExports` shape
  (`values`, `ctors`, `data_constructors`, `classes`, `type_aliases`, `*_origins`).

#### C7. Completion / go-to-definition

- Logic unchanged; they consume the rebuilt `resolution_exports` / indexes.

#### C8. Cleanup

- Remove all `use crate::typechecker::…` from `src/lsp/`.
- `pretty_type` → `Display`; `TypeError`/`TypeWarning`/`Type` → typecheck_db
  equivalents.

## Sequencing

1. **Part A** (typecheck_db capabilities) with new unit tests — no LSP changes,
   nothing else perturbed. Check in.
2. **Part B** (`check_module_ide`). Check in.
3. **Part C** (LSP rewire), feature by feature, keeping `tests/lsp_e2e.rs` green
   throughout. Check in.

## Risks & open items

- **A3 higher-kinded param rendering** — may need kind-pass enrichment; isolate
  and verify against the `MyFunctor` fixture line.
- **Hover doc comments** — confirm source of truth before porting.
- **Per-edit latency** — full re-inference of the focused module should match
  today's LSP; validate on the oa app.
- **DB concurrency** — `Arc<Mutex<TypecheckDb>>` serializes checks; acceptable
  (LSP processes one edit at a time).
- **CLI span-type overhead** — see "Always-on semantics"; make opt-in if
  measurable.
