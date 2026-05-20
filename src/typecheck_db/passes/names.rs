//! M2: the names pipeline — three cacheable passes per declaration.
//!
//! - [`defined_names`]: what names this decl introduces into its module.
//! - [`free_names`]: what external names this decl references.
//! - [`resolve_names`]: resolve each free reference against a [`ModuleScope`].
//!
//! Cache story:
//! - `defined_names` and `free_names` have a single input, the decl source hash.
//! - `resolve_names` depends on `free_names(same decl)` and the input `ModuleScope`.
//!   A body-only edit that doesn't change the set of free names leaves
//!   `resolve_names` cached and its downstream consumers undisturbed.
//!
//! Name binding / shadowing is tracked locally through expression trees: a
//! free reference is only emitted for value names that are not bound by an
//! enclosing lambda / case-alt / let / where / do-bind.

use std::collections::HashSet;

use serde::{Deserialize, Serialize};

use crate::cst::{
    ClassMember, Constraint, DataConstructor, Module, ModuleName, QualifiedIdent, TypeExpr,
};
use crate::interner::{self, Symbol};
use crate::typecheck_db::driver::{CacheOutcome, DriverError, TypecheckDb};
use crate::typecheck_db::ir::{
    Binder, CaseAlternative, Decl, DoStatement, Expr, GuardPattern, GuardedExpr, LetBinding,
    Literal,
};
use crate::typecheck_db::key::{hash_bytes, InputHash, InputHasher, OutputHash, PassKey};

// ============================================================================
// Shared data types
// ============================================================================

/// Which namespace a name lives in.
///
/// Values and constructors occupy distinct namespaces in PureScript, as do
/// types and classes. Operators (value-level vs type-level) are also separate.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub enum NameKind {
    Value,
    Constructor,
    Type,
    Class,
    Op,
    TypeOp,
}

/// One external reference emitted by `free_names`: name plus optional module
/// qualifier, plus which namespace it lives in.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Reference {
    pub kind: NameKind,
    pub module: Option<String>,
    pub name: String,
}

/// A name after resolution: the canonical module it lives in + its kind.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct ResolvedName {
    pub kind: NameKind,
    pub module: String,
    pub name: String,
}

/// Names defined by one decl. Stored sorted so the serialized form is
/// deterministic and its hash is a stable cache input.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct DefinedNames {
    pub names: Vec<(NameKind, String)>,
}

/// External references observed in one decl. Stored sorted for the same
/// reason as `DefinedNames`.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct FreeNames {
    pub refs: Vec<Reference>,
}

/// The outcome of resolving every free reference. Unresolved references
/// are kept so downstream passes can turn them into diagnostics.
#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct ResolvedNames {
    pub resolved: Vec<(Reference, ResolvedName)>,
    pub unresolved: Vec<Reference>,
}

/// What's in scope for a module during `resolve_names`. `locals` are names
/// defined in this module; `imports` come from its `import` declarations
/// (already flattened: map from local binding to where it lives canonically).
///
/// For M2 this is an explicit input — later milestones will build it from
/// `defined_names` outputs of the current module and export records of
/// imported modules.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct ModuleScope {
    pub module: String,
    pub locals: Vec<(NameKind, String)>,
    pub imports: Vec<(Reference, ResolvedName)>,
}

impl ModuleScope {
    pub fn new(module: impl Into<String>) -> Self {
        Self { module: module.into(), ..Self::default() }
    }

    pub fn add_local(&mut self, kind: NameKind, name: impl Into<String>) {
        self.locals.push((kind, name.into()));
    }

    /// Map an imported local binding to its canonical origin.
    pub fn add_import(
        &mut self,
        kind: NameKind,
        local_name: impl Into<String>,
        from_module: impl Into<String>,
        canonical_name: impl Into<String>,
    ) {
        self.imports.push((
            Reference { kind, module: None, name: local_name.into() },
            ResolvedName { kind, module: from_module.into(), name: canonical_name.into() },
        ));
    }

    /// Add a qualified import: `Data.Array.head` in-source → `Data.Array.head`.
    pub fn add_qualified_import(
        &mut self,
        kind: NameKind,
        source_module: impl Into<String>,
        canonical_module: impl Into<String>,
        name: impl Into<String>,
    ) {
        let name: String = name.into();
        self.imports.push((
            Reference { kind, module: Some(source_module.into()), name: name.clone() },
            ResolvedName { kind, module: canonical_module.into(), name },
        ));
    }

    /// Deterministically hash the scope so `resolve_names` can fold it into
    /// its `input_hash`. Sorting guarantees order-insensitivity.
    pub fn hash(&self) -> InputHash {
        let mut locals = self.locals.clone();
        locals.sort();
        let mut imports = self.imports.clone();
        imports.sort();

        let mut h = blake3::Hasher::new();
        h.update(b"ModuleScope\0");
        h.update(self.module.as_bytes());
        h.update(&[0u8]);
        h.update(&(locals.len() as u32).to_le_bytes());
        for (k, n) in &locals {
            h.update(&[*k as u8]);
            h.update(n.as_bytes());
            h.update(&[0u8]);
        }
        h.update(&(imports.len() as u32).to_le_bytes());
        for (r, res) in &imports {
            h.update(&[r.kind as u8]);
            crate::typecheck_db::util::hash_opt_str(&mut h, r.module.as_deref());
            h.update(r.name.as_bytes());
            h.update(&[0u8]);
            h.update(&[res.kind as u8]);
            h.update(res.module.as_bytes());
            h.update(&[0u8]);
            h.update(res.name.as_bytes());
            h.update(&[0u8]);
        }
        *h.finalize().as_bytes()
    }
}

// ============================================================================
// Pass: defined_names
// ============================================================================

pub mod defined_names {
    use super::*;

    pub const PASS_NAME: &str = "defined_names";
    pub const PASS_VERSION: u32 = 1;

    pub fn compute(decl: &Decl) -> DefinedNames {
        let mut out: Vec<(NameKind, String)> = Vec::new();
        match decl {
            Decl::Value { name, .. } | Decl::TypeSignature { name, .. } => {
                out.push((NameKind::Value, sym_to_string(name.value.symbol())));
            }
            Decl::Data { name, constructors, kind_sig, is_role_decl, .. } => {
                if *is_role_decl {
                    // Role declarations reference an existing type, they
                    // don't introduce names.
                } else {
                    out.push((NameKind::Type, sym_to_string(name.value.symbol())));
                    // Kind signatures only introduce the type name, not ctors.
                    if matches!(*kind_sig, crate::cst::KindSigSource::None) {
                        for ctor in constructors {
                            out.push((
                                NameKind::Constructor,
                                sym_to_string(ctor.name.value.symbol()),
                            ));
                        }
                    }
                }
            }
            Decl::TypeAlias { name, .. } => {
                out.push((NameKind::Type, sym_to_string(name.value.symbol())));
            }
            Decl::Newtype { name, constructor, .. } => {
                out.push((NameKind::Type, sym_to_string(name.value.symbol())));
                out.push((NameKind::Constructor, sym_to_string(constructor.value.symbol())));
            }
            Decl::Class { name, members, is_kind_sig, .. } => {
                out.push((NameKind::Class, sym_to_string(name.value.symbol())));
                if !is_kind_sig {
                    for m in members {
                        out.push((NameKind::Value, sym_to_string(m.name.value.symbol())));
                    }
                }
            }
            Decl::Instance { name, .. } | Decl::Derive { name, .. } => {
                if let Some(n) = name {
                    out.push((NameKind::Value, sym_to_string(n.value.symbol())));
                }
            }
            Decl::Fixity { operator, is_type, .. } => {
                let kind = if *is_type { NameKind::TypeOp } else { NameKind::Op };
                out.push((kind, sym_to_string(operator.value.symbol())));
            }
            Decl::Foreign { name, .. } => {
                out.push((NameKind::Value, sym_to_string(name.value.symbol())));
            }
            Decl::ForeignData { name, .. } => {
                out.push((NameKind::Type, sym_to_string(name.value.symbol())));
            }
        }
        out.sort();
        out.dedup();
        DefinedNames { names: out }
    }

    pub fn run(
        db: &mut TypecheckDb,
        module: &str,
        decl_key: &str,
        decl_source_hash: [u8; 32],
        decl: &Decl,
    ) -> Result<(DefinedNames, OutputHash, CacheOutcome), DriverError> {
        let key = PassKey::new(module, decl_key, PASS_NAME);
        let input_hash = InputHasher::new(PASS_NAME, PASS_VERSION)
            .with_source_hash(decl_source_hash)
            .finish();

        if let Some((v, oh)) = db.get_cached::<DefinedNames>(&key, input_hash)? {
            return Ok((v, oh, CacheOutcome::Hit));
        }
        let value = compute(decl);
        let oh = db.put(&key, input_hash, &value)?;
        Ok((value, oh, CacheOutcome::Miss))
    }
}

// ============================================================================
// Pass: free_names
// ============================================================================

pub mod free_names {
    use super::*;

    pub const PASS_NAME: &str = "free_names";
    pub const PASS_VERSION: u32 = 1;

    pub fn compute(decl: &Decl) -> FreeNames {
        let mut col = Collector::default();
        col.visit_decl(decl);
        col.finish()
    }

    pub fn run(
        db: &mut TypecheckDb,
        module: &str,
        decl_key: &str,
        decl_source_hash: [u8; 32],
        decl: &Decl,
    ) -> Result<(FreeNames, OutputHash, CacheOutcome), DriverError> {
        let key = PassKey::new(module, decl_key, PASS_NAME);
        let input_hash = InputHasher::new(PASS_NAME, PASS_VERSION)
            .with_source_hash(decl_source_hash)
            .finish();

        if let Some((v, oh)) = db.get_cached::<FreeNames>(&key, input_hash)? {
            return Ok((v, oh, CacheOutcome::Hit));
        }
        let value = compute(decl);
        let oh = db.put(&key, input_hash, &value)?;
        Ok((value, oh, CacheOutcome::Miss))
    }
}

// ============================================================================
// Pass: resolve_names
// ============================================================================

pub mod resolve_names {
    use super::*;
    use crate::typecheck_db::store::DepEdge;

    pub const PASS_NAME: &str = "resolve_names";
    // v2: the ModuleScope hasher's `ImportRef.module` encoding gained a
    // 0/1 discriminator, invalidating v1 cache rows.
    pub const PASS_VERSION: u32 = 2;

    /// Given already-computed `free_names` + a module scope, produce a
    /// resolution for each reference.
    pub fn compute(free: &FreeNames, scope: &ModuleScope) -> ResolvedNames {
        let mut resolved = Vec::new();
        let mut unresolved = Vec::new();

        let local_set: HashSet<(NameKind, &str)> = scope
            .locals
            .iter()
            .map(|(k, n)| (*k, n.as_str()))
            .collect();

        for r in &free.refs {
            // Qualified references always resolve "through" the qualifier:
            // for M2, the qualifier is taken as the canonical module unless
            // the scope provides an explicit remapping (e.g. an `import ...
            // as Q` alias).
            if let Some(qual) = &r.module {
                if let Some((_, res)) = scope
                    .imports
                    .iter()
                    .find(|(lhs, _)| lhs == r)
                {
                    resolved.push((r.clone(), res.clone()));
                } else {
                    resolved.push((
                        r.clone(),
                        ResolvedName { kind: r.kind, module: qual.clone(), name: r.name.clone() },
                    ));
                }
                continue;
            }

            // Unqualified: look at locals, then imports.
            if local_set.contains(&(r.kind, r.name.as_str())) {
                resolved.push((
                    r.clone(),
                    ResolvedName { kind: r.kind, module: scope.module.clone(), name: r.name.clone() },
                ));
                continue;
            }
            if let Some((_, res)) = scope.imports.iter().find(|(lhs, _)| lhs == r) {
                resolved.push((r.clone(), res.clone()));
                continue;
            }
            unresolved.push(r.clone());
        }

        resolved.sort();
        unresolved.sort();
        ResolvedNames { resolved, unresolved }
    }

    pub fn run(
        db: &mut TypecheckDb,
        module: &str,
        decl_key: &str,
        free: &FreeNames,
        free_names_output_hash: OutputHash,
        scope: &ModuleScope,
    ) -> Result<(ResolvedNames, OutputHash, CacheOutcome), DriverError> {
        let key = PassKey::new(module, decl_key, PASS_NAME);
        let scope_hash = scope.hash();
        let mut hasher = InputHasher::new(PASS_NAME, PASS_VERSION).with_source_hash(scope_hash);
        hasher.add_dep(module, decl_key, free_names::PASS_NAME, free_names_output_hash);
        let input_hash = hasher.finish();

        if let Some((v, oh)) = db.get_cached::<ResolvedNames>(&key, input_hash)? {
            return Ok((v, oh, CacheOutcome::Hit));
        }
        let value = compute(free, scope);
        let oh = db.put(&key, input_hash, &value)?;
        db.put_deps(
            &key,
            &[DepEdge {
                dep_module: module.to_string(),
                dep_decl: decl_key.to_string(),
                dep_pass: free_names::PASS_NAME.to_string(),
            }],
        )?;
        Ok((value, oh, CacheOutcome::Miss))
    }
}

// ============================================================================
// free_names collector: walks CST bodies tracking local bindings
// ============================================================================

#[derive(Default)]
struct Collector {
    refs: HashSet<Reference>,
    /// Stack of locally-bound value names. A name at any level shadows any
    /// outer reference.
    value_scopes: Vec<HashSet<String>>,
}

impl Collector {
    fn finish(self) -> FreeNames {
        let mut refs: Vec<Reference> = self.refs.into_iter().collect();
        refs.sort();
        FreeNames { refs }
    }

    fn push_scope(&mut self) {
        self.value_scopes.push(HashSet::new());
    }

    fn pop_scope(&mut self) {
        self.value_scopes.pop();
    }

    fn bind_value(&mut self, name: &str) {
        if let Some(top) = self.value_scopes.last_mut() {
            top.insert(name.to_string());
        }
    }

    fn is_value_bound(&self, name: &str) -> bool {
        self.value_scopes.iter().any(|s| s.contains(name))
    }

    fn emit(&mut self, r: Reference) {
        self.refs.insert(r);
    }

    // -- decl-level entry points ------------------------------------------------

    fn visit_decl(&mut self, decl: &Decl) {
        match decl {
            Decl::Value { binders, guarded, where_clause, .. } => {
                self.push_scope();
                // where-clause value names are in scope for both the body and
                // each other — collect them up front.
                for wb in where_clause {
                    if let LetBinding::Value { binder, .. } = wb {
                        self.bind_binder_names(binder);
                    }
                }
                for b in binders {
                    self.bind_binder_names(b);
                    self.visit_binder_for_refs(b);
                }
                self.visit_guarded(guarded);
                for wb in where_clause {
                    self.visit_let_binding(wb);
                }
                self.pop_scope();
            }
            Decl::TypeSignature { ty, .. } => {
                self.visit_type(ty);
            }
            Decl::Data { constructors, kind_type, type_var_kind_anns, .. } => {
                for ctor in constructors {
                    self.visit_ctor(ctor);
                }
                if let Some(k) = kind_type {
                    self.visit_type(k);
                }
                for ann in type_var_kind_anns.iter().flatten() {
                    self.visit_type(ann);
                }
            }
            Decl::TypeAlias { ty, type_var_kind_anns, .. } => {
                self.visit_type(ty);
                for ann in type_var_kind_anns.iter().flatten() {
                    self.visit_type(ann);
                }
            }
            Decl::Newtype { ty, type_var_kind_anns, .. } => {
                self.visit_type(ty);
                for ann in type_var_kind_anns.iter().flatten() {
                    self.visit_type(ann);
                }
            }
            Decl::Class { constraints, members, kind_type, type_var_kind_anns, .. } => {
                for c in constraints {
                    self.visit_constraint(c);
                }
                for m in members {
                    self.visit_class_member(m);
                }
                if let Some(k) = kind_type {
                    self.visit_type(k);
                }
                for ann in type_var_kind_anns.iter().flatten() {
                    self.visit_type(ann);
                }
            }
            Decl::Instance { constraints, class_name, types, members, .. } => {
                let module_opt = if class_name.module.is_unresolved() {
                    None
                } else {
                    Some(sym_to_string(class_name.module.symbol()))
                };
                self.emit(Reference {
                    kind: NameKind::Class,
                    module: module_opt,
                    name: sym_to_string(class_name.name.symbol()),
                });
                for c in constraints {
                    self.visit_constraint(c);
                }
                for t in types {
                    self.visit_type(t);
                }
                // Instance method bodies are top-level-ish: start with an
                // empty scope stack so their recursion / free vars are
                // tracked the same way top-level values are.
                for m in members {
                    self.visit_decl(m);
                }
            }
            Decl::Derive { constraints, class_name, types, .. } => {
                let module_opt = if class_name.module.is_unresolved() {
                    None
                } else {
                    Some(sym_to_string(class_name.module.symbol()))
                };
                self.emit(Reference {
                    kind: NameKind::Class,
                    module: module_opt,
                    name: sym_to_string(class_name.name.symbol()),
                });
                for c in constraints {
                    self.visit_constraint(c);
                }
                for t in types {
                    self.visit_type(t);
                }
            }
            Decl::Fixity { target, is_type, .. } => {
                self.emit(Reference {
                    kind: if *is_type { NameKind::Type } else { NameKind::Value },
                    module: target.module.map(sym_to_string),
                    name: sym_to_string(target.name),
                });
            }
            Decl::Foreign { ty, .. } => self.visit_type(ty),
            Decl::ForeignData { kind, .. } => self.visit_type(kind),
        }
    }

    // -- expressions ------------------------------------------------------------

    fn visit_expr(&mut self, expr: &Expr) {
        match expr {
            Expr::Var { name, .. } => {
                // `Expr::Var.name` is now `Resolved<ValueName>` —
                // module is always present (sentinel for unresolved).
                let module_opt = if name.module.is_unresolved() {
                    None
                } else {
                    Some(sym_to_string(name.module.symbol()))
                };
                let name_str = sym_to_string(name.name.symbol());
                if module_opt.is_none() && self.is_value_bound(&name_str) {
                    return;
                }
                self.emit(Reference {
                    kind: NameKind::Value,
                    module: module_opt,
                    name: name_str,
                });
            }
            Expr::Constructor { name, .. } => {
                let module_opt = if name.module.is_unresolved() {
                    None
                } else {
                    Some(sym_to_string(name.module.symbol()))
                };
                self.emit(Reference {
                    kind: NameKind::Constructor,
                    module: module_opt,
                    name: sym_to_string(name.name.symbol()),
                });
            }
            Expr::Literal { lit, .. } => self.visit_literal(lit),
            Expr::App { func, arg, .. } => {
                self.visit_expr(func);
                self.visit_expr(arg);
            }
            Expr::VisibleTypeApp { func, ty, .. } => {
                self.visit_expr(func);
                self.visit_type(ty);
            }
            Expr::Lambda { binders, body, .. } => {
                self.push_scope();
                for b in binders {
                    self.bind_binder_names(b);
                    self.visit_binder_for_refs(b);
                }
                self.visit_expr(body);
                self.pop_scope();
            }
            // `Expr::Op` / `OpParens` / `BacktickApp` don't exist
            // in `ir::Expr` — the lowering pass rebrackets them into
            // plain applications before names runs.
            Expr::If { cond, then_expr, else_expr, .. } => {
                self.visit_expr(cond);
                self.visit_expr(then_expr);
                self.visit_expr(else_expr);
            }
            Expr::Case { exprs, alts, .. } => {
                for e in exprs {
                    self.visit_expr(e);
                }
                for alt in alts {
                    self.visit_case_alt(alt);
                }
            }
            Expr::Let { bindings, body, .. } => {
                self.push_scope();
                for b in bindings {
                    if let LetBinding::Value { binder, .. } = b {
                        self.bind_binder_names(binder);
                    }
                }
                for b in bindings {
                    self.visit_let_binding(b);
                }
                self.visit_expr(body);
                self.pop_scope();
            }
            Expr::Do { statements, .. } => {
                self.push_scope();
                for s in statements {
                    self.visit_do_stmt(s);
                }
                self.pop_scope();
            }
            Expr::Ado { statements, result, .. } => {
                self.push_scope();
                for s in statements {
                    self.visit_do_stmt(s);
                }
                self.visit_expr(result);
                self.pop_scope();
            }
            Expr::Record { fields, .. } => {
                for f in fields {
                    if let Some(v) = &f.value {
                        self.visit_expr(v);
                    }
                    if let Some(ty) = &f.type_ann {
                        self.visit_type(ty);
                    }
                }
            }
            Expr::RecordAccess { expr, .. } => self.visit_expr(expr),
            Expr::RecordUpdate { expr, updates, .. } => {
                self.visit_expr(expr);
                for u in updates {
                    self.visit_expr(&u.value);
                }
            }
            Expr::Parens { expr, .. } => self.visit_expr(expr),
            Expr::TypeAnnotation { expr, ty, .. } => {
                self.visit_expr(expr);
                self.visit_type(ty);
            }
            Expr::Array { elements, .. } => {
                for e in elements {
                    self.visit_expr(e);
                }
            }
            Expr::Negate { expr, .. } => self.visit_expr(expr),
            Expr::AsPattern { name, pattern, .. } => {
                // The `name@` side rebinds — treat as a local of whatever
                // value name appears there. This branch is rare at the expr
                // layer (parser uses it for do-bind sugar).
                self.visit_expr(name);
                self.visit_expr(pattern);
            }
            Expr::Wildcard { .. } | Expr::Hole { .. } => {}
        }
    }

    fn visit_literal(&mut self, lit: &Literal) {
        if let Literal::Array(elems) = lit {
            for e in elems {
                self.visit_expr(e);
            }
        }
    }

    fn emit_op_ref(&mut self, qi: &QualifiedIdent) {
        self.emit(Reference {
            kind: NameKind::Op,
            module: qi.module.map(sym_to_string),
            name: sym_to_string(qi.name),
        });
    }

    // -- guarded / case-alt / do / let ------------------------------------------

    fn visit_guarded(&mut self, g: &GuardedExpr) {
        match g {
            GuardedExpr::Unconditional(e) => self.visit_expr(e),
            GuardedExpr::Guarded(guards) => {
                for guard in guards {
                    self.push_scope();
                    for p in &guard.patterns {
                        match p {
                            GuardPattern::Boolean(e) => self.visit_expr(e),
                            GuardPattern::Pattern(binder, e) => {
                                self.bind_binder_names(binder);
                                self.visit_binder_for_refs(binder);
                                self.visit_expr(e);
                            }
                        }
                    }
                    self.visit_expr(&guard.expr);
                    self.pop_scope();
                }
            }
        }
    }

    fn visit_case_alt(&mut self, alt: &CaseAlternative) {
        self.push_scope();
        for b in &alt.binders {
            self.bind_binder_names(b);
            self.visit_binder_for_refs(b);
        }
        self.visit_guarded(&alt.result);
        self.pop_scope();
    }

    fn visit_do_stmt(&mut self, s: &DoStatement) {
        match s {
            DoStatement::Bind { binder, expr, .. } => {
                // The expr is evaluated in the enclosing scope, then the
                // binder names are added to the scope for subsequent stmts.
                self.visit_expr(expr);
                self.bind_binder_names(binder);
                self.visit_binder_for_refs(binder);
            }
            DoStatement::Let { bindings, .. } => {
                for b in bindings {
                    if let LetBinding::Value { binder, .. } = b {
                        self.bind_binder_names(binder);
                    }
                }
                for b in bindings {
                    self.visit_let_binding(b);
                }
            }
            DoStatement::Discard { expr, .. } => self.visit_expr(expr),
        }
    }

    fn visit_let_binding(&mut self, b: &LetBinding) {
        match b {
            LetBinding::Value { expr, binder, .. } => {
                self.visit_binder_for_refs(binder);
                self.visit_expr(expr);
            }
            LetBinding::Signature { ty, .. } => self.visit_type(ty),
        }
    }

    // -- binders ---------------------------------------------------------------

    /// Record all value-name bindings this pattern introduces into the
    /// current scope.
    fn bind_binder_names(&mut self, binder: &Binder) {
        match binder {
            Binder::Wildcard { .. } | Binder::Literal { .. } => {}
            Binder::Var { name, .. } => self.bind_value(&sym_to_string(name.value.symbol())),
            Binder::Constructor { args, .. } => {
                for a in args {
                    self.bind_binder_names(a);
                }
            }
            Binder::Record { fields, .. } => {
                for f in fields {
                    match &f.binder {
                        Some(b) => self.bind_binder_names(b),
                        // Pun `{ x }` binds `x`.
                        None => self.bind_value(&sym_to_string(f.label.value.symbol())),
                    }
                }
            }
            Binder::As { name, binder, .. } => {
                self.bind_value(&sym_to_string(name.value.symbol()));
                self.bind_binder_names(binder);
            }
            Binder::Parens { binder, .. } => self.bind_binder_names(binder),
            Binder::Array { elements, .. } => {
                for e in elements {
                    self.bind_binder_names(e);
                }
            }
            // `Binder::Op` doesn't exist in `ir::Binder`.
            Binder::Typed { binder, .. } => self.bind_binder_names(binder),
        }
    }

    /// Collect references appearing *inside* a pattern: constructor names,
    /// operators, type annotations. Binder value-names are bindings, not
    /// references, and are handled by `bind_binder_names`.
    fn visit_binder_for_refs(&mut self, binder: &Binder) {
        match binder {
            Binder::Wildcard { .. } | Binder::Var { .. } => {}
            Binder::Literal { lit, .. } => self.visit_literal(lit),
            Binder::Constructor { name, args, .. } => {
                let module_opt = if name.module.is_unresolved() {
                    None
                } else {
                    Some(sym_to_string(name.module.symbol()))
                };
                self.emit(Reference {
                    kind: NameKind::Constructor,
                    module: module_opt,
                    name: sym_to_string(name.name.symbol()),
                });
                for a in args {
                    self.visit_binder_for_refs(a);
                }
            }
            Binder::Record { fields, .. } => {
                for f in fields {
                    if let Some(b) = &f.binder {
                        self.visit_binder_for_refs(b);
                    }
                }
            }
            Binder::As { binder, .. } | Binder::Parens { binder, .. } => {
                self.visit_binder_for_refs(binder)
            }
            Binder::Array { elements, .. } => {
                for e in elements {
                    self.visit_binder_for_refs(e);
                }
            }
            // `Binder::Op` doesn't exist in `ir::Binder` — the
            // lowering pass rebrackets operator patterns.
            Binder::Typed { binder, ty, .. } => {
                self.visit_binder_for_refs(binder);
                self.visit_type(ty);
            }
        }
    }

    // -- types & constraints ----------------------------------------------------

    fn visit_type(&mut self, ty: &TypeExpr) {
        match ty {
            TypeExpr::Var { .. }
            | TypeExpr::Hole { .. }
            | TypeExpr::Wildcard { .. }
            | TypeExpr::StringLiteral { .. }
            | TypeExpr::IntLiteral { .. } => {}
            TypeExpr::Constructor { name, .. } => {
                let qi = name.to_qi();
                self.emit(Reference {
                    kind: NameKind::Type,
                    module: qi.module.map(sym_to_string),
                    name: sym_to_string(qi.name),
                });
            }
            TypeExpr::App { constructor, arg, .. } => {
                self.visit_type(constructor);
                self.visit_type(arg);
            }
            TypeExpr::Function { from, to, .. } => {
                self.visit_type(from);
                self.visit_type(to);
            }
            TypeExpr::Forall { vars, ty, .. } => {
                for (_, _, kind) in vars {
                    if let Some(k) = kind {
                        self.visit_type(k);
                    }
                }
                self.visit_type(ty);
            }
            TypeExpr::Constrained { constraints, ty, .. } => {
                for c in constraints {
                    self.visit_constraint(c);
                }
                self.visit_type(ty);
            }
            TypeExpr::Record { fields, .. } => {
                for f in fields {
                    self.visit_type(&f.ty);
                }
            }
            TypeExpr::Row { fields, tail, .. } => {
                for f in fields {
                    self.visit_type(&f.ty);
                }
                if let Some(t) = tail {
                    self.visit_type(t);
                }
            }
            TypeExpr::Parens { ty, .. } => self.visit_type(ty),
            TypeExpr::TypeOp { left, op, right, .. } => {
                self.visit_type(left);
                let qi = op.value.to_qi();
                self.emit(Reference {
                    kind: NameKind::TypeOp,
                    module: qi.module.map(sym_to_string),
                    name: sym_to_string(qi.name),
                });
                self.visit_type(right);
            }
            TypeExpr::Kinded { ty, kind, .. } => {
                self.visit_type(ty);
                self.visit_type(kind);
            }
            TypeExpr::ArrayPattern { elements, .. } => {
                for e in elements {
                    self.visit_type(e);
                }
            }
            TypeExpr::AsPattern { ty, .. } => self.visit_type(ty),
        }
    }

    fn visit_constraint(&mut self, c: &Constraint) {
        self.emit(Reference {
            kind: NameKind::Class,
            module: qi_module(&c.class.to_qi()),
            name: sym_to_string(c.class.name_symbol()),
        });
        for a in &c.args {
            self.visit_type(a);
        }
    }

    fn visit_ctor(&mut self, ctor: &DataConstructor) {
        for f in &ctor.fields {
            self.visit_type(f);
        }
    }

    fn visit_class_member(&mut self, m: &ClassMember) {
        self.visit_type(&m.ty);
    }
}

// ============================================================================
// helpers
// ============================================================================

fn sym_to_string(sym: Symbol) -> String {
    crate::typecheck_db::util::resolve_symbol(sym)
}

fn qi_module(qi: &QualifiedIdent) -> Option<String> {
    qi.module.map(sym_to_string)
}

/// Hash a decl's source slice using the module source. The caller is
/// responsible for providing the correct slice range — typically the decl's
/// `span`.
pub fn hash_decl_source(source: &str) -> [u8; 32] {
    hash_bytes(source.as_bytes())
}

/// Conventional decl-key for a top-level declaration: use the first defined
/// name (sorted) so instance blocks without a name still get a stable id
/// derived from their span, prefixed with "_inst_".
pub fn decl_key_for(decl: &Decl) -> String {
    let defined = defined_names::compute(decl);
    if let Some((_, n)) = defined.names.first() {
        return n.clone();
    }
    // Instance/Derive with no explicit name — fall back to span-based id.
    let span = decl.span();
    format!("_anon@{}..{}", span.start, span.end)
}

/// Convenience: look up a module name's canonical string form.
pub fn module_name_string(m: &ModuleName) -> String {
    m.parts
        .iter()
        .map(|p| crate::typecheck_db::util::resolve_symbol(*p))
        .collect::<Vec<_>>()
        .join(".")
}

/// Convenience: a shallow summary of every decl in a module, paired with
/// source hashes sliced from `source`. Useful for drivers that want to
/// iterate every decl with the right cache inputs without re-implementing
/// span slicing.
pub fn decls_with_source_hashes<'a>(
    module: &'a Module,
    source: &'a str,
) -> Vec<(&'a crate::cst::Decl, [u8; 32])> {
    module
        .decls
        .iter()
        .map(|d| {
            let span = d.span();
            let start = span.start.min(source.len());
            let end = span.end.min(source.len());
            let slice = &source[start..end];
            (d, hash_bytes(slice.as_bytes()))
        })
        .collect()
}

// ============================================================================
// tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse;

    // IR lowering is strict: any `Op` / `OpParens` / `BacktickApp`
    // / `Binder::Op` that survives desugar produces a
    // `LoweringError`. Test helpers must run the full desugar
    // pipeline before handing the CST to `lower_module`.
    fn lower_after_desugar(module: crate::cst::Module) -> crate::typecheck_db::ir::Module {
        use crate::typecheck_db::desugar::{
            desugar_module, fixity_table_from_decls, DesugarContext,
        };
        let (fixity_table, module_fixity_hash) = fixity_table_from_decls(&module.decls);
        let ctx = DesugarContext { module_fixity_hash, fixity_table, qualified_fixity_table: Default::default() };
        let decls = desugar_module(module.decls.clone(), &ctx);
        let desugared = crate::cst::Module {
            span: module.span,
            name: module.name,
            exports: module.exports,
            imports: module.imports,
            decls,
            comments: module.comments,
            doc_comments: module.doc_comments,
        };
        crate::typecheck_db::ir::lower_module(desugared).expect("cst → ir lowering")
    }

    fn parse_single_decl(src: &str) -> Decl {
        let module = parse(src).expect("parse");
        let ir_module = lower_after_desugar(module);
        ir_module
            .decls
            .into_iter()
            .find(|d| !matches!(d, Decl::TypeSignature { .. }))
            .expect("at least one non-signature decl")
    }

    fn parse_decl_by_index(src: &str, i: usize) -> Decl {
        let module = parse(src).expect("parse");
        let ir_module = lower_after_desugar(module);
        ir_module.decls.into_iter().nth(i).expect("decl at index")
    }

    // ---- defined_names -------------------------------------------------------

    #[test]
    fn defined_names_value() {
        let d = parse_single_decl("module M where\nfoo = 1\n");
        let names = defined_names::compute(&d).names;
        assert_eq!(names, vec![(NameKind::Value, "foo".into())]);
    }

    #[test]
    fn defined_names_data_has_ctors() {
        let d = parse_single_decl("module M where\ndata Maybe a = Nothing | Just a\n");
        let names = defined_names::compute(&d).names;
        assert_eq!(
            names,
            vec![
                (NameKind::Constructor, "Just".into()),
                (NameKind::Constructor, "Nothing".into()),
                (NameKind::Type, "Maybe".into()),
            ]
        );
    }

    #[test]
    fn defined_names_newtype() {
        let d = parse_single_decl("module M where\nnewtype Age = Age Int\n");
        let names = defined_names::compute(&d).names;
        assert_eq!(
            names,
            vec![
                (NameKind::Constructor, "Age".into()),
                (NameKind::Type, "Age".into()),
            ]
        );
    }

    #[test]
    fn defined_names_class_has_methods() {
        let d = parse_single_decl(
            "module M where\nclass Eq a where\n  eq :: a -> a -> Boolean\n",
        );
        let names = defined_names::compute(&d).names;
        assert!(names.contains(&(NameKind::Class, "Eq".into())));
        assert!(names.contains(&(NameKind::Value, "eq".into())));
    }

    // ---- free_names ----------------------------------------------------------

    #[test]
    fn free_names_value_binding() {
        let d = parse_decl_by_index("module M where\nfoo = add one two\n", 0);
        let refs = free_names::compute(&d).refs;
        let names: HashSet<(NameKind, Option<String>, String)> = refs
            .into_iter()
            .map(|r| (r.kind, r.module, r.name))
            .collect();
        assert!(names.contains(&(NameKind::Value, None, "add".into())));
        assert!(names.contains(&(NameKind::Value, None, "one".into())));
        assert!(names.contains(&(NameKind::Value, None, "two".into())));
    }

    #[test]
    fn free_names_lambda_shadows_outer() {
        // `x` inside the lambda is bound; it must not escape as a free ref.
        let d = parse_decl_by_index("module M where\nfoo = \\x -> x\n", 0);
        let refs = free_names::compute(&d).refs;
        assert!(refs
            .iter()
            .all(|r| !(r.kind == NameKind::Value && r.module.is_none() && r.name == "x")));
    }

    #[test]
    fn free_names_outer_ref_unshadowed_captures() {
        let d = parse_decl_by_index("module M where\nfoo = \\x -> y\n", 0);
        let refs = free_names::compute(&d).refs;
        assert!(refs.iter().any(|r| {
            r.kind == NameKind::Value && r.module.is_none() && r.name == "y"
        }));
    }

    #[test]
    fn free_names_case_binders_shadow() {
        let src = "module M where\nfoo x = case x of\n  Just y -> y\n  Nothing -> zero\n";
        let d = parse_decl_by_index(src, 0);
        let refs = free_names::compute(&d).refs;
        // `y` is bound by the case alt, must not appear as a free value ref.
        assert!(refs
            .iter()
            .all(|r| !(r.kind == NameKind::Value && r.module.is_none() && r.name == "y")));
        // `Just` and `Nothing` are constructors — must appear.
        assert!(refs
            .iter()
            .any(|r| r.kind == NameKind::Constructor && r.name == "Just"));
        assert!(refs
            .iter()
            .any(|r| r.kind == NameKind::Constructor && r.name == "Nothing"));
        // `zero` is a real free reference.
        assert!(refs
            .iter()
            .any(|r| r.kind == NameKind::Value && r.name == "zero"));
    }

    #[test]
    fn free_names_let_binds_locals() {
        let src = "module M where\nfoo = let x = one in x\n";
        let d = parse_decl_by_index(src, 0);
        let refs = free_names::compute(&d).refs;
        assert!(refs
            .iter()
            .all(|r| !(r.kind == NameKind::Value && r.name == "x")));
        assert!(refs.iter().any(|r| r.name == "one"));
    }

    #[test]
    fn free_names_where_clause_binds_locals() {
        let src = "module M where\nfoo = x + y\n  where\n  x = one\n  y = two\n";
        let d = parse_decl_by_index(src, 0);
        let refs = free_names::compute(&d).refs;
        // `x` and `y` are defined in the where-clause and must not be free.
        assert!(refs
            .iter()
            .all(|r| !(r.kind == NameKind::Value && (r.name == "x" || r.name == "y"))));
    }

    #[test]
    fn free_names_do_bind_introduces_local() {
        let src = "module M where\nfoo = do\n  x <- step\n  pure x\n";
        let d = parse_decl_by_index(src, 0);
        let refs = free_names::compute(&d).refs;
        assert!(refs
            .iter()
            .all(|r| !(r.kind == NameKind::Value && r.module.is_none() && r.name == "x")));
        assert!(refs.iter().any(|r| r.name == "step"));
        assert!(refs.iter().any(|r| r.name == "pure"));
    }

    #[test]
    fn free_names_type_signature_captures_types() {
        let src = "module M where\nfoo :: Int -> Boolean\n";
        let d = parse_decl_by_index(src, 0);
        let refs = free_names::compute(&d).refs;
        assert!(refs
            .iter()
            .any(|r| r.kind == NameKind::Type && r.name == "Int"));
        assert!(refs
            .iter()
            .any(|r| r.kind == NameKind::Type && r.name == "Boolean"));
    }

    #[test]
    fn free_names_qualified_ref_carries_module() {
        let src = "module M where\nfoo = Data.Array.head xs\n";
        let d = parse_decl_by_index(src, 0);
        let refs = free_names::compute(&d).refs;
        assert!(refs.iter().any(|r| {
            r.kind == NameKind::Value
                && r.module.as_deref() == Some("Data.Array")
                && r.name == "head"
        }));
    }

    // ---- resolve_names -------------------------------------------------------

    #[test]
    fn resolve_local_and_imported() {
        let free = FreeNames {
            refs: vec![
                Reference { kind: NameKind::Value, module: None, name: "local".into() },
                Reference { kind: NameKind::Value, module: None, name: "imported".into() },
                Reference { kind: NameKind::Value, module: None, name: "missing".into() },
            ],
        };
        let mut scope = ModuleScope::new("M");
        scope.add_local(NameKind::Value, "local");
        scope.add_import(NameKind::Value, "imported", "Other", "imported");

        let res = resolve_names::compute(&free, &scope);
        assert_eq!(res.unresolved.len(), 1);
        assert_eq!(res.unresolved[0].name, "missing");

        let found: std::collections::HashMap<String, ResolvedName> = res
            .resolved
            .into_iter()
            .map(|(r, res)| (r.name, res))
            .collect();
        assert_eq!(found.get("local").unwrap().module, "M");
        assert_eq!(found.get("imported").unwrap().module, "Other");
    }

    #[test]
    fn resolve_qualified_uses_qualifier_by_default() {
        let free = FreeNames {
            refs: vec![Reference {
                kind: NameKind::Value,
                module: Some("Data.Array".into()),
                name: "head".into(),
            }],
        };
        let scope = ModuleScope::new("M");
        let res = resolve_names::compute(&free, &scope);
        assert_eq!(res.resolved.len(), 1);
        assert_eq!(res.unresolved.len(), 0);
        assert_eq!(res.resolved[0].1.module, "Data.Array");
    }

    #[test]
    fn resolve_qualified_alias_remap() {
        let free = FreeNames {
            refs: vec![Reference {
                kind: NameKind::Value,
                module: Some("Arr".into()),
                name: "head".into(),
            }],
        };
        let mut scope = ModuleScope::new("M");
        scope.add_qualified_import(NameKind::Value, "Arr", "Data.Array", "head");
        let res = resolve_names::compute(&free, &scope);
        assert_eq!(res.resolved[0].1.module, "Data.Array");
    }

    // ---- caching / invalidation ---------------------------------------------

    fn run_decl_pipeline(
        db: &mut TypecheckDb,
        module: &str,
        decl_key: &str,
        decl: &Decl,
        src_hash: [u8; 32],
        scope: &ModuleScope,
    ) -> (OutputHash, OutputHash, CacheOutcome, CacheOutcome) {
        let (_fn, free_hash, fn_outcome) =
            free_names::run(db, module, decl_key, src_hash, decl).unwrap();
        let fn_value = free_names::compute(decl);
        let (_rn, rn_hash, rn_outcome) =
            resolve_names::run(db, module, decl_key, &fn_value, free_hash, scope).unwrap();
        (free_hash, rn_hash, fn_outcome, rn_outcome)
    }

    #[test]
    fn resolve_names_caches_when_free_names_unchanged() {
        let mut db = TypecheckDb::open_in_memory().unwrap();
        let decl = parse_decl_by_index("module M where\nfoo = add one two\n", 0);
        let src_hash = hash_decl_source("foo = add one two");
        let mut scope = ModuleScope::new("M");
        scope.add_import(NameKind::Value, "add", "Prelude", "add");
        scope.add_import(NameKind::Value, "one", "Prelude", "one");
        scope.add_import(NameKind::Value, "two", "Prelude", "two");

        let (f1, r1, fo1, ro1) = run_decl_pipeline(&mut db, "M", "foo", &decl, src_hash, &scope);
        assert_eq!(fo1, CacheOutcome::Miss);
        assert_eq!(ro1, CacheOutcome::Miss);

        // Same inputs — both passes hit.
        let (f2, r2, fo2, ro2) = run_decl_pipeline(&mut db, "M", "foo", &decl, src_hash, &scope);
        assert_eq!(fo2, CacheOutcome::Hit);
        assert_eq!(ro2, CacheOutcome::Hit);
        assert_eq!(f1, f2);
        assert_eq!(r1, r2);
    }

    #[test]
    fn body_edit_without_free_name_change_preserves_resolve_names_cache() {
        // Swapping the *order* of calls to the same names changes the decl
        // source but not the set of free names — so free_names' output hash
        // is unchanged and resolve_names stays cached.
        let mut db = TypecheckDb::open_in_memory().unwrap();
        let mut scope = ModuleScope::new("M");
        scope.add_import(NameKind::Value, "add", "Prelude", "add");
        scope.add_import(NameKind::Value, "one", "Prelude", "one");
        scope.add_import(NameKind::Value, "two", "Prelude", "two");

        let decl_v1 = parse_decl_by_index("module M where\nfoo = add one two\n", 0);
        let h_v1 = hash_decl_source("foo = add one two");
        let (free_h1, res_h1, _, _) =
            run_decl_pipeline(&mut db, "M", "foo", &decl_v1, h_v1, &scope);

        // Edited body: different source, same free names.
        let decl_v2 = parse_decl_by_index("module M where\nfoo = add two one\n", 0);
        let h_v2 = hash_decl_source("foo = add two one");
        assert_ne!(h_v1, h_v2);

        let (_fn_v2, free_h2, free_outcome) =
            free_names::run(&mut db, "M", "foo", h_v2, &decl_v2).unwrap();
        assert_eq!(free_outcome, CacheOutcome::Miss); // different source hash => recompute
        assert_eq!(free_h1, free_h2); // but same output hash (refs unchanged)

        // Because free_names' output_hash is unchanged, resolve_names'
        // input_hash is unchanged, and so we hit the cache.
        let free_v2 = free_names::compute(&decl_v2);
        let (_rn, res_h2, res_outcome) =
            resolve_names::run(&mut db, "M", "foo", &free_v2, free_h2, &scope).unwrap();
        assert_eq!(res_outcome, CacheOutcome::Hit);
        assert_eq!(res_h1, res_h2);
    }

    #[test]
    fn body_edit_that_changes_free_names_invalidates_resolve_names() {
        let mut db = TypecheckDb::open_in_memory().unwrap();
        let mut scope = ModuleScope::new("M");
        scope.add_import(NameKind::Value, "add", "Prelude", "add");
        scope.add_import(NameKind::Value, "mul", "Prelude", "mul");
        scope.add_import(NameKind::Value, "one", "Prelude", "one");
        scope.add_import(NameKind::Value, "two", "Prelude", "two");

        let decl_v1 = parse_decl_by_index("module M where\nfoo = add one two\n", 0);
        let h_v1 = hash_decl_source("foo = add one two");
        let (free_h1, res_h1, _, _) =
            run_decl_pipeline(&mut db, "M", "foo", &decl_v1, h_v1, &scope);

        // Swap `add` for `mul` — new free-name set.
        let decl_v2 = parse_decl_by_index("module M where\nfoo = mul one two\n", 0);
        let h_v2 = hash_decl_source("foo = mul one two");
        let (free_h2, res_h2, _, res_outcome) =
            run_decl_pipeline(&mut db, "M", "foo", &decl_v2, h_v2, &scope);

        assert_ne!(free_h1, free_h2);
        assert_ne!(res_h1, res_h2);
        assert_eq!(res_outcome, CacheOutcome::Miss);
    }

    #[test]
    fn scope_change_invalidates_resolve_names_only() {
        let mut db = TypecheckDb::open_in_memory().unwrap();
        let decl = parse_decl_by_index("module M where\nfoo = add one two\n", 0);
        let src_hash = hash_decl_source("foo = add one two");

        let mut scope_v1 = ModuleScope::new("M");
        scope_v1.add_import(NameKind::Value, "add", "Prelude", "add");
        scope_v1.add_import(NameKind::Value, "one", "Prelude", "one");
        scope_v1.add_import(NameKind::Value, "two", "Prelude", "two");

        let (free_h1, res_h1, _, _) =
            run_decl_pipeline(&mut db, "M", "foo", &decl, src_hash, &scope_v1);

        // Same decl but `add` now resolves from a different module.
        let mut scope_v2 = ModuleScope::new("M");
        scope_v2.add_import(NameKind::Value, "add", "Other.Add", "add");
        scope_v2.add_import(NameKind::Value, "one", "Prelude", "one");
        scope_v2.add_import(NameKind::Value, "two", "Prelude", "two");

        let free_v2 = free_names::compute(&decl);
        let (_fn, free_h2, free_outcome) =
            free_names::run(&mut db, "M", "foo", src_hash, &decl).unwrap();
        assert_eq!(free_outcome, CacheOutcome::Hit); // unrelated to scope
        assert_eq!(free_h1, free_h2);

        let (_rn, res_h2, res_outcome) =
            resolve_names::run(&mut db, "M", "foo", &free_v2, free_h2, &scope_v2).unwrap();
        assert_eq!(res_outcome, CacheOutcome::Miss);
        assert_ne!(res_h1, res_h2);
    }

    #[test]
    fn dependents_of_reveals_resolve_names_depending_on_free_names() {
        let mut db = TypecheckDb::open_in_memory().unwrap();
        let decl = parse_decl_by_index("module M where\nfoo = add one two\n", 0);
        let src_hash = hash_decl_source("foo = add one two");
        let mut scope = ModuleScope::new("M");
        scope.add_import(NameKind::Value, "add", "Prelude", "add");
        scope.add_import(NameKind::Value, "one", "Prelude", "one");
        scope.add_import(NameKind::Value, "two", "Prelude", "two");

        run_decl_pipeline(&mut db, "M", "foo", &decl, src_hash, &scope);

        let deps = db.store().dependents_of("M", "foo", free_names::PASS_NAME).unwrap();
        assert_eq!(deps.len(), 1);
        assert_eq!(deps[0].pass, resolve_names::PASS_NAME);
        assert_eq!(deps[0].decl, "foo");
    }
}
