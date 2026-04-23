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
    let mut errors: Vec<KindError> = Vec::new();
    let mut ctx = Ctx { arity_env: &arity_env, class_env: &class_env, errors: &mut errors };

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
                if let Some(&expected) = self.arity_env.get(&name.name.symbol()) {
                    if args.len() > expected {
                        self.errors.push(KindError {
                            span: *span,
                            kind: KindErrorKind::KindsDoNotUnify {
                                head: resolve(name.name.symbol()),
                                expected,
                                got: args.len(),
                            },
                        });
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
