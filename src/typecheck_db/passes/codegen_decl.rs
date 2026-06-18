//! `codegen_decl` pass: per-declaration JavaScript codegen, cached in the
//! typecheck_db. Produces one `CodegenOutput` (rendered JS text + assembly
//! metadata) per PureScript declaration (or value-equation group).
//!
//! The heavy lifting (IR → JS translation) lives in `crate::codegen::decl`;
//! this module owns the cache key/version, serialization, and module-level
//! assembly of per-decl text into a final ES module.

use serde::{Deserialize, Serialize};

use std::collections::HashMap;

use crate::codegen::common::module_name_str_to_js;
use crate::codegen::decl::{
    codegen_class_decl, codegen_data_decl, codegen_derive_decl, codegen_foreign_decl,
    codegen_instance_decl, codegen_newtype_decl, codegen_value_group, DeclCgCtx, DerivedTypeInfo,
    GenDecl,
};
use crate::codegen::js_ast::{JsModule, JsStmt};
use crate::codegen::printer::{print_module, print_stmts};
use crate::span::Span;
use crate::typecheck_db::driver::{CacheOutcome, DriverError, TypecheckDb};
use crate::typecheck_db::ir;
use crate::typecheck_db::key::{hash_bytes, InputHasher, OutputHash, PassKey};
use crate::typecheck_db::passes::constraints::ResolvedDict;

pub const PASS_NAME: &str = "codegen_decl";
pub const PASS_VERSION: u32 = 1;

/// One emitted top-level JS binding, as rendered text.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct JsUnit {
    pub js_name: String,
    pub text: String,
}

/// Cached codegen result for a single declaration.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct CodegenOutput {
    pub units: Vec<JsUnit>,
    /// Module parts of every external module referenced by this decl.
    pub external_refs: Vec<Vec<String>>,
    /// (js_name, optional original-PS-name for `as` rename) to export.
    pub exports: Vec<(String, Option<String>)>,
    /// `$foreign` members referenced / re-exported.
    pub foreign_refs: Vec<String>,
}

fn gen_to_output(gen: GenDecl) -> CodegenOutput {
    let units = gen
        .units
        .into_iter()
        .map(|u| JsUnit { js_name: u.js_name, text: print_stmts(&u.stmts) })
        .collect();
    CodegenOutput {
        units,
        external_refs: gen.external_refs,
        exports: gen.exports,
        foreign_refs: gen.foreign_refs,
    }
}

fn input_hash(
    decl_source_hash: [u8; 32],
    module_context_hash: [u8; 32],
    scheme_dep: Option<OutputHash>,
) -> [u8; 32] {
    let mut hasher = InputHasher::new(PASS_NAME, PASS_VERSION)
        .with_source_hash(decl_source_hash)
        .with_module_context(module_context_hash);
    if let Some(oh) = scheme_dep {
        hasher.add_dep("_self", "_scheme", "infer_value_scc", oh);
    }
    hasher.finish()
}

/// Cache-aware codegen for a value-equation group sharing `decl_key`.
#[allow(clippy::too_many_arguments)]
pub fn run_value_group(
    db: &mut TypecheckDb,
    decl_key: &str,
    decl_source_hash: [u8; 32],
    module_context_hash: [u8; 32],
    scheme_dep: Option<OutputHash>,
    equations: &[&ir::Decl],
    ctx: &DeclCgCtx,
    constraint_dicts: &HashMap<Span, Vec<ResolvedDict>>,
    leading_constraints: &[crate::typecheck_db::types::Constraint],
) -> Result<(CodegenOutput, OutputHash, CacheOutcome), DriverError> {
    let key = PassKey::new(ctx.module, decl_key, PASS_NAME);
    let ih = input_hash(decl_source_hash, module_context_hash, scheme_dep);

    if let Some((value, oh)) = db.get_cached::<CodegenOutput>(&key, ih)? {
        return Ok((value, oh, CacheOutcome::Hit));
    }

    let value =
        gen_to_output(codegen_value_group(equations, ctx, constraint_dicts, leading_constraints));
    let oh = db.put(&key, ih, &value)?;
    Ok((value, oh, CacheOutcome::Miss))
}

/// Cache-aware codegen for a `class` declaration (method accessors).
pub fn run_class_decl(
    db: &mut TypecheckDb,
    module: &str,
    decl_key: &str,
    decl_source_hash: [u8; 32],
    module_context_hash: [u8; 32],
    decl: &ir::Decl,
) -> Result<(CodegenOutput, OutputHash, CacheOutcome), DriverError> {
    let key = PassKey::new(module, decl_key, PASS_NAME);
    let ih = input_hash(decl_source_hash, module_context_hash, None);
    if let Some((value, oh)) = db.get_cached::<CodegenOutput>(&key, ih)? {
        return Ok((value, oh, CacheOutcome::Hit));
    }
    let value = gen_to_output(codegen_class_decl(decl));
    let oh = db.put(&key, ih, &value)?;
    Ok((value, oh, CacheOutcome::Miss))
}

/// Cache-aware codegen for an `instance` declaration (dictionary object).
/// Not cached through the DB yet because the instance method dicts come from
/// in-memory schemes; computed fresh each run.
pub fn run_instance_decl(
    decl: &ir::Decl,
    ctx: &DeclCgCtx,
    method_dicts: &HashMap<String, HashMap<Span, Vec<ResolvedDict>>>,
    method_leading: &HashMap<String, Vec<String>>,
) -> CodegenOutput {
    gen_to_output(codegen_instance_decl(decl, ctx, method_dicts, method_leading))
}

/// Codegen for a `derive instance` / `derive newtype instance` declaration.
pub fn run_derive_decl(
    decl: &ir::Decl,
    ctx: &DeclCgCtx,
    info: Option<&DerivedTypeInfo>,
) -> CodegenOutput {
    gen_to_output(codegen_derive_decl(decl, ctx, info))
}

/// Cache-aware codegen for a non-value declaration (data / newtype / foreign).
/// These translate without an expression context.
pub fn run_nonvalue_decl(
    db: &mut TypecheckDb,
    module: &str,
    decl_key: &str,
    decl_source_hash: [u8; 32],
    module_context_hash: [u8; 32],
    decl: &ir::Decl,
) -> Result<(CodegenOutput, OutputHash, CacheOutcome), DriverError> {
    let key = PassKey::new(module, decl_key, PASS_NAME);
    let ih = input_hash(decl_source_hash, module_context_hash, None);

    if let Some((value, oh)) = db.get_cached::<CodegenOutput>(&key, ih)? {
        return Ok((value, oh, CacheOutcome::Hit));
    }

    let gen: GenDecl = match decl {
        ir::Decl::Data { .. } => codegen_data_decl(decl),
        ir::Decl::Newtype { .. } => codegen_newtype_decl(decl),
        ir::Decl::Foreign { .. } => codegen_foreign_decl(decl),
        _ => GenDecl::default(),
    };
    let value = gen_to_output(gen);
    let oh = db.put(&key, ih, &value)?;
    Ok((value, oh, CacheOutcome::Miss))
}

/// Assemble per-decl `CodegenOutput`s into a final ES module text.
///
/// Phase-1 trivial assembler: dedups imports from `external_refs`, concatenates
/// rendered unit text in the order given, and builds the export block. A
/// `$foreign` import + re-export block is emitted when `foreign_members` is
/// non-empty.
pub fn assemble_module(outputs: &[CodegenOutput]) -> String {
    // Foreign members are re-exported from the FFI companion module.
    let mut foreign_members: Vec<String> = Vec::new();
    for out in outputs {
        for f in &out.foreign_refs {
            if !foreign_members.contains(f) {
                foreign_members.push(f.clone());
            }
        }
    }
    let foreign_members = &foreign_members;

    // Dedup external module references, preserving first-seen order.
    let mut import_parts: Vec<Vec<String>> = Vec::new();
    for out in outputs {
        for parts in &out.external_refs {
            if !import_parts.contains(parts) {
                import_parts.push(parts.clone());
            }
        }
    }
    let imports: Vec<JsStmt> = import_parts
        .iter()
        .map(|parts| {
            let dotted = parts.join(".");
            JsStmt::Import {
                name: module_name_str_to_js(&dotted),
                path: format!("../{dotted}/index.js"),
            }
        })
        .collect();

    // Concatenate rendered unit bodies.
    let mut body_text = String::new();
    for out in outputs {
        for unit in &out.units {
            body_text.push_str(&unit.text);
        }
    }

    // Union exports across decls (preserving order).
    let mut exports: Vec<(String, Option<String>)> = Vec::new();
    for out in outputs {
        for e in &out.exports {
            if !exports.iter().any(|(n, _)| n == &e.0) {
                exports.push(e.clone());
            }
        }
    }

    let has_ffi = !foreign_members.is_empty();
    let module = JsModule {
        imports,
        body: if body_text.is_empty() {
            vec![]
        } else {
            vec![JsStmt::RawJs(body_text.trim_end().to_string())]
        },
        exports,
        foreign_exports: foreign_members.to_vec(),
        foreign_module_path: if has_ffi {
            Some("./foreign.js".to_string())
        } else {
            None
        },
        reexports: vec![],
    };
    print_module(&module)
}

/// Hash a declaration's source slice for the `codegen_decl` input hash.
pub fn source_slice_hash(source: &str, spans: &[(usize, usize)]) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(b"codegen_decl_source_v1");
    for (start, end) in spans {
        let slice = source.get(*start..*end).unwrap_or("");
        h.update(&(slice.len() as u32).to_le_bytes());
        h.update(slice.as_bytes());
    }
    let _ = hash_bytes; // keep import used across cfgs
    *h.finalize().as_bytes()
}
