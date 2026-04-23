//! Standalone kind-check pass.
//!
//! Runs after import resolution and the per-decl non-value passes.
//! Walks every type-application site in the module and verifies arity
//! against the head's declared kind. Reports `KindsDoNotUnify` when:
//!   - A type / class / alias / foreign-data is applied to MORE
//!     arguments than its declared arity allows.
//!   - A constraint in a value signature uses a class with the wrong
//!     number of arguments.
//!
//! Deliberately *under-approximates*: it doesn't perform full kind
//! unification (which would require porting the old typechecker's
//! kind solver). The arity check alone catches the bulk of
//! KindsDoNotUnify fixtures whose root cause is a class or type
//! constructor being applied with the wrong number of args.
//!
//! Designed as a separate pass: takes a `&cst::Module` plus a kind
//! environment built from local decls + the cross-module registry,
//! produces a `Vec<KindError>`. No mutable state shared with
//! inference; the caller drains errors into `ModuleCheckResult`.

use std::collections::HashMap;

use serde::{Deserialize, Serialize};

use crate::cst;
use crate::interner::Symbol;
use crate::span::Span;
use crate::typecheck_db::module_registry::ModuleRegistry;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct KindError {
    pub span: Span,
    pub kind: KindErrorKind,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum KindErrorKind {
    /// `Foo` was applied to `got` arguments but its declared arity is
    /// `expected`. Used for both type constructors and class
    /// constraints — distinguished by the call site.
    KindsDoNotUnify {
        head: String,
        expected: usize,
        got: usize,
    },
}

/// Per-parameter expected kind structure. We approximate kinds by
/// "arrow count" (number of `->` arrows at the top level): `Type` = 0,
/// `Type -> Type` = 1, `(Type -> Type) -> Type` = 1, etc. Coarse but
/// good enough to catch `Syn Int` when `Syn (a :: Type -> Type)` is
/// the declared shape.
#[derive(Debug, Clone, Copy)]
struct ParamKind {
    /// Number of arrows the param expects. None = no kind annotation
    /// (treat as wildcard).
    arrows: Option<usize>,
}

/// Build the param-kind environment for a module: every nominal type
/// constructor's per-param expected kind structure, plus aliases'.
fn build_param_kinds(
    module: &cst::Module,
    registry: &ModuleRegistry,
) -> HashMap<Symbol, Vec<ParamKind>> {
    let mut env: HashMap<Symbol, Vec<ParamKind>> = HashMap::new();

    // For nominal types (data/newtype/class), unannotated params
    // default to Type (arrow_count = 0) — the var will be used in
    // constructor fields which require Type-kind. For type aliases
    // there's no such default (RHS may have any kind), so callers
    // pass `default_to_type = false`.
    //
    // ALSO: when the var is used as a type constructor anywhere in
    // the RHS (`newtype Ap f a = Ap (f a)` — `f` is used as a
    // ctor), default-to-Type is suppressed. Would otherwise flag
    // `Ap Id1 a` as a mismatch (Id1 is higher-kinded, f's inferred
    // kind is `Type -> Type`).
    let collect_with_default = |vars: &[Symbol],
                                anns: &[Option<Box<cst::TypeExpr>>],
                                default_to_type: bool,
                                bodies: &[cst::TypeExpr]|
     -> Vec<ParamKind> {
        let (hkt_vars, poly_vars) = if default_to_type {
            classify_var_usage(bodies, vars)
        } else {
            (std::collections::HashSet::new(), std::collections::HashSet::new())
        };
        vars.iter()
            .zip(anns.iter())
            .map(|(v, opt)| ParamKind {
                arrows: match (opt.as_deref(), default_to_type) {
                    (Some(te), _) => Some(arrow_count(te)),
                    (None, true) if hkt_vars.contains(v) => None,
                    (None, true) if poly_vars.contains(v) => None,
                    (None, true) => Some(0),
                    (None, false) => None,
                },
            })
            .collect()
    };

    // Types that have a sibling standalone kind signature (`data Foo
    // :: Kind -> Kind`). Default-to-Type is suppressed for these
    // because the standalone kind could declare higher-kinded
    // params that we don't parse here.
    let mut has_standalone_kind: std::collections::HashSet<Symbol> =
        std::collections::HashSet::new();
    for d in &module.decls {
        match d {
            cst::Decl::Data { name, kind_sig, .. }
                if !matches!(kind_sig, cst::KindSigSource::None) =>
            {
                has_standalone_kind.insert(name.value.symbol());
            }
            cst::Decl::Class { name, is_kind_sig: true, .. } => {
                has_standalone_kind.insert(name.value.symbol());
            }
            _ => {}
        }
    }

    for d in &module.decls {
        match d {
            cst::Decl::Data {
                name,
                type_vars,
                type_var_kind_anns,
                constructors,
                kind_sig: cst::KindSigSource::None,
                is_role_decl: false,
                kind_type: None,
                ..
            } => {
                let default = !has_standalone_kind.contains(&name.value.symbol());
                let vars: Vec<Symbol> =
                    type_vars.iter().map(|v| v.value.symbol()).collect();
                let bodies: Vec<cst::TypeExpr> = constructors
                    .iter()
                    .flat_map(|c| c.fields.iter().cloned())
                    .collect();
                env.insert(
                    name.value.symbol(),
                    collect_with_default(&vars, type_var_kind_anns, default, &bodies),
                );
            }
            cst::Decl::Newtype { name, type_vars, type_var_kind_anns, ty, .. } => {
                let default = !has_standalone_kind.contains(&name.value.symbol());
                let vars: Vec<Symbol> =
                    type_vars.iter().map(|v| v.value.symbol()).collect();
                env.insert(
                    name.value.symbol(),
                    collect_with_default(&vars, type_var_kind_anns, default, std::slice::from_ref(ty)),
                );
            }
            cst::Decl::TypeAlias { name, type_vars, type_var_kind_anns, .. } => {
                let vars: Vec<Symbol> =
                    type_vars.iter().map(|v| v.value.symbol()).collect();
                env.insert(
                    name.value.symbol(),
                    collect_with_default(&vars, type_var_kind_anns, false, &[]),
                );
            }
            cst::Decl::Class {
                name,
                type_vars,
                type_var_kind_anns,
                members,
                is_kind_sig: false,
                kind_type: None,
                ..
            } => {
                let default = !has_standalone_kind.contains(&name.value.symbol());
                let vars: Vec<Symbol> =
                    type_vars.iter().map(|v| v.value.symbol()).collect();
                let bodies: Vec<cst::TypeExpr> =
                    members.iter().map(|m| m.ty.clone()).collect();
                env.insert(
                    name.value.symbol(),
                    collect_with_default(&vars, type_var_kind_anns, default, &bodies),
                );
            }
            _ => {}
        }
    }

    // We don't have per-param kind annotations from the registry,
    // only arities, so imported types contribute no annotations —
    // their App-sites won't trigger an annotation-based check.
    let _ = registry;
    env
}

/// Hardcoded arities for the most common Prim type constructors.
/// `Prim` is implicitly imported by every user module but doesn't
/// flow through the registry path here.
fn prim_arities() -> &'static [(&'static str, usize)] {
    &[
        ("Int", 0),
        ("Number", 0),
        ("String", 0),
        ("Char", 0),
        ("Boolean", 0),
        ("Type", 0),
        ("Constraint", 0),
        ("Symbol", 0),
        ("Array", 1),
        ("Function", 2),
        ("Record", 1),
        ("Row", 1),
        ("Partial", 0),
    ]
}

/// Build the kind environment for a module. Only NOMINAL type-level
/// names go in: data / newtype / foreign-data / class. Type aliases
/// are deliberately excluded — their RHS may have higher kind, so a
/// 0-arg alias like `type CONST = Const` (Const :: Type -> k -> Type)
/// can legitimately be applied to args.
fn build_arity_env(
    module: &cst::Module,
    registry: &ModuleRegistry,
) -> HashMap<Symbol, usize> {
    let mut env: HashMap<Symbol, usize> = HashMap::new();

    // Local aliases — used as a SET of names to skip (we treat
    // any reference to a local alias as un-checkable arity).
    let local_aliases: std::collections::HashSet<Symbol> = module
        .decls
        .iter()
        .filter_map(|d| match d {
            cst::Decl::TypeAlias { name, .. } => Some(name.value.symbol()),
            _ => None,
        })
        .collect();

    // 0) Implicit Prim imports.
    for (name, arity) in prim_arities() {
        env.insert(crate::interner::intern(name), *arity);
    }

    // 1) Imports — only direct imports contribute to scope.
    for imp in &module.imports {
        let name = imp
            .module
            .parts
            .iter()
            .map(|p| crate::interner::resolve(*p).unwrap_or_default())
            .collect::<Vec<_>>()
            .join(".");
        if let Some(exports) = registry.get(&name) {
            for (tname, arity) in &exports.type_arities {
                let sym = crate::interner::intern(tname);
                // Skip if (a) this is a local alias name or (b) it's
                // an alias on the imported side. We can't tell aliases
                // apart from data types in the registry's arity map,
                // so the safest move is to skip imported names that
                // also appear in `type_aliases`.
                if local_aliases.contains(&sym) {
                    continue;
                }
                if exports.type_aliases.contains_key(tname) {
                    continue;
                }
                env.insert(sym, *arity);
            }
        }
    }

    // 2) Local nominal decls win — but skip type aliases.
    for d in &module.decls {
        match d {
            cst::Decl::Data {
                name,
                type_vars,
                kind_sig: cst::KindSigSource::None,
                is_role_decl: false,
                kind_type: None,
                ..
            } => {
                env.insert(name.value.symbol(), type_vars.len());
            }
            cst::Decl::Newtype { name, type_vars, .. } => {
                env.insert(name.value.symbol(), type_vars.len());
            }
            cst::Decl::Class {
                name,
                type_vars,
                is_kind_sig: false,
                kind_type: None,
                ..
            } => {
                env.insert(name.value.symbol(), type_vars.len());
            }
            cst::Decl::ForeignData { name, kind, .. } => {
                env.insert(name.value.symbol(), arrow_count(kind));
            }
            _ => {}
        }
    }

    env
}

/// Class arity environment — same as type arities but keyed only on
/// classes. Used for constraint-arg arity checks (where the class
/// might share a name with a non-class type, or might be a
/// constraint that doesn't appear in the type-arity registry).
fn build_class_arity_env(
    module: &cst::Module,
    registry: &ModuleRegistry,
) -> HashMap<Symbol, usize> {
    let mut env: HashMap<Symbol, usize> = HashMap::new();

    for imp in &module.imports {
        let name = imp
            .module
            .parts
            .iter()
            .map(|p| crate::interner::resolve(*p).unwrap_or_default())
            .collect::<Vec<_>>()
            .join(".");
        if let Some(exports) = registry.get(&name) {
            for (cname, info) in &exports.classes {
                let sym = crate::interner::intern(cname);
                env.insert(sym, info.type_vars.len());
            }
        }
    }

    for d in &module.decls {
        if let cst::Decl::Class { name, type_vars, is_kind_sig: false, .. } = d {
            env.insert(name.value.symbol(), type_vars.len());
        }
    }

    env
}

/// Top-level entry point. Walks every type-application site in the
/// module and reports kind-arity mismatches.
pub fn check_module(
    module: &cst::Module,
    registry: &ModuleRegistry,
) -> Vec<KindError> {
    let arity_env = build_arity_env(module, registry);
    let class_env = build_class_arity_env(module, registry);
    let param_kinds = build_param_kinds(module, registry);
    let mut errors: Vec<KindError> = Vec::new();
    let mut ctx = Ctx {
        arity_env: &arity_env,
        class_env: &class_env,
        param_kinds: &param_kinds,
        errors: &mut errors,
    };

    for d in &module.decls {
        match d {
            cst::Decl::Data { constructors, .. } => {
                for c in constructors {
                    for f in &c.fields {
                        ctx.check_type(f);
                    }
                }
            }
            cst::Decl::Newtype { ty, .. } => ctx.check_type(ty),
            cst::Decl::TypeAlias { ty, .. } => ctx.check_type(ty),
            cst::Decl::TypeSignature { ty, .. } => ctx.check_type(ty),
            cst::Decl::Foreign { ty, .. } => ctx.check_type(ty),
            cst::Decl::Class { constraints, members, .. } => {
                for c in constraints {
                    ctx.check_constraint(c);
                }
                for m in members {
                    ctx.check_type(&m.ty);
                }
            }
            cst::Decl::Instance { constraints, types, members, .. } => {
                for c in constraints {
                    ctx.check_constraint(c);
                }
                for t in types {
                    ctx.check_type(t);
                }
                for m in members {
                    if let cst::Decl::TypeSignature { ty, .. } = m {
                        ctx.check_type(ty);
                    }
                }
            }
            cst::Decl::Derive { constraints, types, .. } => {
                for c in constraints {
                    ctx.check_constraint(c);
                }
                for t in types {
                    ctx.check_type(t);
                }
            }
            _ => {}
        }
    }

    errors
}

struct Ctx<'a> {
    arity_env: &'a HashMap<Symbol, usize>,
    class_env: &'a HashMap<Symbol, usize>,
    param_kinds: &'a HashMap<Symbol, Vec<ParamKind>>,
    errors: &'a mut Vec<KindError>,
}

impl<'a> Ctx<'a> {
    /// Walk a type expression and check every constructor application
    /// for arity correctness.
    fn check_type(&mut self, te: &cst::TypeExpr) {
        // Peel App chains: `f x y z` → head=f, args=[x,y,z].
        let (head, args) = peel_app(te);

        if let cst::TypeExpr::Constructor { span, name } = head {
            // Only check unqualified or same-name lookups.
            if name.module.is_none() {
                let sym = name.name.symbol();
                if let Some(&expected) = self.arity_env.get(&sym) {
                    if args.len() > expected {
                        self.errors.push(KindError {
                            span: *span,
                            kind: KindErrorKind::KindsDoNotUnify {
                                head: resolve(sym),
                                expected,
                                got: args.len(),
                            },
                        });
                    }
                }
                // Per-parameter kind annotations: when the head's
                // type vars carry explicit kinds, verify each
                // supplied arg's structural kind matches.
                if let Some(params) = self.param_kinds.get(&sym) {
                    for (i, arg) in args.iter().enumerate() {
                        if let Some(p) = params.get(i) {
                            if let Some(expected_arrows) = p.arrows {
                                if let Some(actual_arrows) = self.infer_arg_arrows(arg) {
                                    if actual_arrows != expected_arrows {
                                        self.errors.push(KindError {
                                            span: arg.span(),
                                            kind: KindErrorKind::KindsDoNotUnify {
                                                head: resolve(sym),
                                                expected: expected_arrows,
                                                got: actual_arrows,
                                            },
                                        });
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        // Recurse into the head AND every argument so nested
        // applications also get arity-checked.
        match te {
            cst::TypeExpr::App { constructor, arg, .. } => {
                self.check_type(constructor);
                self.check_type(arg);
            }
            cst::TypeExpr::Function { from, to, .. } => {
                self.check_type(from);
                self.check_type(to);
            }
            cst::TypeExpr::Forall { ty, vars, .. } => {
                for (_, _, k) in vars {
                    if let Some(k) = k {
                        self.check_type(k);
                    }
                }
                self.check_type(ty);
            }
            cst::TypeExpr::Constrained { constraints, ty, .. } => {
                for c in constraints {
                    self.check_constraint(c);
                }
                self.check_type(ty);
            }
            cst::TypeExpr::Record { fields, .. } => {
                for f in fields {
                    self.check_type(&f.ty);
                }
            }
            cst::TypeExpr::Row { fields, tail, .. } => {
                for f in fields {
                    self.check_type(&f.ty);
                }
                if let Some(t) = tail {
                    self.check_type(t);
                }
            }
            cst::TypeExpr::Parens { ty, .. } => self.check_type(ty),
            cst::TypeExpr::TypeOp { left, right, .. } => {
                self.check_type(left);
                self.check_type(right);
            }
            cst::TypeExpr::Kinded { ty, kind, .. } => {
                self.check_type(ty);
                self.check_type(kind);
            }
            cst::TypeExpr::ArrayPattern { elements, .. } => {
                for e in elements {
                    self.check_type(e);
                }
            }
            cst::TypeExpr::AsPattern { ty, .. } => self.check_type(ty),
            cst::TypeExpr::Constructor { .. }
            | cst::TypeExpr::Var { .. }
            | cst::TypeExpr::Hole { .. }
            | cst::TypeExpr::Wildcard { .. }
            | cst::TypeExpr::StringLiteral { .. }
            | cst::TypeExpr::IntLiteral { .. } => {}
        }
    }

    /// Infer the arrow-count of an argument's kind. `Type` (a
    /// fully-applied 0-arity ctor like Int) → 0 arrows. `Array` (1
    /// param, fully unapplied) → 1 arrow. Returns None when we
    /// can't tell (alias references, type variables, holes,
    /// wildcards, qualified imports we don't have arities for).
    fn infer_arg_arrows(&self, te: &cst::TypeExpr) -> Option<usize> {
        let (head, args) = peel_app(te);
        match head {
            cst::TypeExpr::Constructor { name, .. } => {
                if name.module.is_some() {
                    // Imported, qualified ref — we don't have full
                    // kinds. Skip.
                    return None;
                }
                let sym = name.name.symbol();
                let arity = self.arity_env.get(&sym).copied()?;
                if args.len() > arity {
                    // Over-applied; the over-application is reported
                    // separately so don't double-flag here.
                    return None;
                }
                Some(arity - args.len())
            }
            cst::TypeExpr::Function { .. }
            | cst::TypeExpr::Forall { .. }
            | cst::TypeExpr::Constrained { .. }
            | cst::TypeExpr::Record { .. }
            | cst::TypeExpr::Row { .. } => Some(0),
            cst::TypeExpr::StringLiteral { .. }
            | cst::TypeExpr::IntLiteral { .. } => Some(0),
            _ => None,
        }
    }

    /// Constraint arity check: a class declared with N type params
    /// must be applied with exactly N arguments.
    fn check_constraint(&mut self, c: &cst::Constraint) {
        // Recurse through args first so nested arity issues surface.
        for a in &c.args {
            self.check_type(a);
        }
        if c.class.module.is_some() {
            // Imported class — we still want to check arity if we have
            // it in the env (build_class_arity_env collected those).
        }
        if let Some(&expected) = self.class_env.get(&c.class.name.symbol()) {
            if c.args.len() != expected {
                self.errors.push(KindError {
                    span: c.span,
                    kind: KindErrorKind::KindsDoNotUnify {
                        head: resolve(c.class.name.symbol()),
                        expected,
                        got: c.args.len(),
                    },
                });
            }
        }
    }
}

fn peel_app(te: &cst::TypeExpr) -> (&cst::TypeExpr, Vec<&cst::TypeExpr>) {
    let mut args: Vec<&cst::TypeExpr> = Vec::new();
    let mut cur = te;
    loop {
        match cur {
            cst::TypeExpr::App { constructor, arg, .. } => {
                args.push(arg);
                cur = constructor;
            }
            cst::TypeExpr::Parens { ty, .. } => cur = ty,
            _ => break,
        }
    }
    args.reverse();
    (cur, args)
}

/// Walk `te` and classify each `vars` entry's usage. Result:
/// `hkt` holds vars used as a type constructor (`f a` → `f`).
/// `poly` holds vars whose kind can't be defaulted to `Type` — either
/// they were used as the arg to a type variable (like `a` in `f a`),
/// or they appear inside a kind annotation. The remainder have
/// default kind `Type`.
fn classify_var_usage(
    bodies: &[cst::TypeExpr],
    vars: &[Symbol],
) -> (std::collections::HashSet<Symbol>, std::collections::HashSet<Symbol>) {
    let mut hkt: std::collections::HashSet<Symbol> =
        std::collections::HashSet::new();
    let mut poly: std::collections::HashSet<Symbol> =
        std::collections::HashSet::new();
    for b in bodies {
        walk_for_var_usage(b, vars, &mut hkt, &mut poly);
    }
    (hkt, poly)
}

fn walk_for_var_usage(
    te: &cst::TypeExpr,
    vars: &[Symbol],
    hkt: &mut std::collections::HashSet<Symbol>,
    poly: &mut std::collections::HashSet<Symbol>,
) {
    match te {
        cst::TypeExpr::App { .. } => {
            let (head, args) = peel_app(te);
            let var_head = match head {
                cst::TypeExpr::Var { name, .. } => {
                    let sym = name.value.symbol();
                    if vars.contains(&sym) {
                        hkt.insert(sym);
                        true
                    } else {
                        false
                    }
                }
                _ => false,
            };
            if var_head {
                // Args to a type-variable head have polymorphic kind.
                for a in &args {
                    if let cst::TypeExpr::Var { name, .. } = a {
                        let sym = name.value.symbol();
                        if vars.contains(&sym) {
                            poly.insert(sym);
                        }
                    }
                    walk_for_var_usage(a, vars, hkt, poly);
                }
            } else {
                walk_for_var_usage(head, vars, hkt, poly);
                for a in args {
                    walk_for_var_usage(a, vars, hkt, poly);
                }
            }
        }
        cst::TypeExpr::Function { from, to, .. } => {
            walk_for_var_usage(from, vars, hkt, poly);
            walk_for_var_usage(to, vars, hkt, poly);
        }
        cst::TypeExpr::Forall { ty, vars: qvars, .. } => {
            let shadowed: Vec<Symbol> =
                qvars.iter().map(|(v, _, _)| v.value.symbol()).collect();
            let sub_vars: Vec<Symbol> =
                vars.iter().copied().filter(|v| !shadowed.contains(v)).collect();
            walk_for_var_usage(ty, &sub_vars, hkt, poly);
        }
        cst::TypeExpr::Constrained { constraints, ty, .. } => {
            for c in constraints {
                for a in &c.args {
                    walk_for_var_usage(a, vars, hkt, poly);
                }
            }
            walk_for_var_usage(ty, vars, hkt, poly);
        }
        cst::TypeExpr::Record { fields, .. } => {
            for f in fields {
                walk_for_var_usage(&f.ty, vars, hkt, poly);
            }
        }
        cst::TypeExpr::Row { fields, tail, .. } => {
            for f in fields {
                walk_for_var_usage(&f.ty, vars, hkt, poly);
            }
            if let Some(t) = tail {
                walk_for_var_usage(t, vars, hkt, poly);
            }
        }
        cst::TypeExpr::Parens { ty, .. } | cst::TypeExpr::Kinded { ty, .. } => {
            walk_for_var_usage(ty, vars, hkt, poly);
        }
        cst::TypeExpr::TypeOp { left, right, .. } => {
            walk_for_var_usage(left, vars, hkt, poly);
            walk_for_var_usage(right, vars, hkt, poly);
        }
        _ => {}
    }
}

/// Approximate kind arity from a kind type expression. Counts the
/// number of `->` arrows at the top level. `Type` → 0, `Type -> Type`
/// → 1, `(Type -> Type) -> Type` → 1.
fn arrow_count(te: &cst::TypeExpr) -> usize {
    match te {
        cst::TypeExpr::Function { to, .. } => 1 + arrow_count(to),
        cst::TypeExpr::Parens { ty, .. } => arrow_count(ty),
        cst::TypeExpr::Forall { ty, .. } => arrow_count(ty),
        _ => 0,
    }
}

fn resolve(sym: Symbol) -> String {
    crate::interner::resolve(sym).unwrap_or_default()
}
