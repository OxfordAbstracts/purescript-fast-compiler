//! Serializable type representation for per-decl cache blobs.
//!
//! Distinct from [`crate::typechecker::types::Type`]:
//! - No unification variables — cached outputs are fully zonked.
//! - No interner `Symbol` — names are plain `String` so blobs are portable
//!   across processes (SQLite-backed cache, LSP restarts, different intern
//!   tables).
//! - `Serialize`/`Deserialize` so bincode can round-trip outputs.
//!
//! This module also provides a structural converter from `cst::TypeExpr` so
//! passes can produce a `Type` without threading the full
//! `typechecker::convert` machinery.

use std::collections::HashMap;
use std::fmt;

use serde::{Deserialize, Serialize};

use crate::cst;
use crate::interner;

/// A (module, name) pair, with the module optional.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct QName {
    pub module: Option<String>,
    pub name: String,
}

impl QName {
    pub fn unqualified(name: impl Into<String>) -> Self {
        Self { module: None, name: name.into() }
    }

    pub fn qualified(module: impl Into<String>, name: impl Into<String>) -> Self {
        Self { module: Some(module.into()), name: name.into() }
    }
}

impl fmt::Display for QName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(m) = &self.module {
            write!(f, "{}.{}", m, self.name)
        } else {
            write!(f, "{}", self.name)
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Var(n) => write!(f, "{}", n),
            Type::Con(q) => write!(f, "{}", q),
            Type::App(g, a) => write!(f, "({} {})", g, a),
            Type::Fun(a, b) => write!(f, "({} -> {})", a, b),
            Type::Forall(vars, body) => {
                write!(f, "forall")?;
                for (n, _, _) in vars {
                    write!(f, " {}", n)?;
                }
                write!(f, ". {}", body)
            }
            Type::Constrained(cs, body) => {
                for (i, c) in cs.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", c.class)?;
                    for a in &c.args {
                        write!(f, " {}", a)?;
                    }
                }
                write!(f, " => {}", body)
            }
            Type::Record(fields, tail) => {
                write!(f, "{{ ")?;
                for (i, (l, t)) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{} :: {}", l, t)?;
                }
                if let Some(t) = tail {
                    write!(f, " | {}", t)?;
                }
                write!(f, " }}")
            }
            Type::Row(fields, tail) => {
                write!(f, "(")?;
                for (i, (l, t)) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{} :: {}", l, t)?;
                }
                if let Some(t) = tail {
                    write!(f, " | {}", t)?;
                }
                write!(f, ")")
            }
            Type::Hole(n) => write!(f, "?{}", n),
            Type::Wildcard => write!(f, "_"),
            Type::TypeString(s) => write!(f, "\"{}\"", s),
            Type::TypeInt(n) => write!(f, "{}", n),
            Type::Kinded(t, k) => write!(f, "({} :: {})", t, k),
            Type::Unif(id) => write!(f, "?u{}", id),
        }
    }
}

/// A type — used for both value-level types and kinds. PureScript treats
/// kinds as types; this wire type mirrors that.
///
/// The `Unif` variant is only meaningful *during* inference. Any `Type`
/// stored in a cache blob must be fully zonked — no remaining unification
/// variables.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Type {
    Var(String),
    Con(QName),
    App(Box<Type>, Box<Type>),
    Fun(Box<Type>, Box<Type>),
    /// Quantifier vars: `(name, visible, optional_kind)`.
    Forall(Vec<(String, bool, Option<Box<Type>>)>, Box<Type>),
    Constrained(Vec<Constraint>, Box<Type>),
    /// Closed or open record type: `{ l1 :: T1, l2 :: T2 | r }`.
    Record(Vec<(String, Type)>, Option<Box<Type>>),
    /// Row type: `( l1 :: T1, l2 :: T2 | r )`.
    Row(Vec<(String, Type)>, Option<Box<Type>>),
    Hole(String),
    Wildcard,
    TypeString(String),
    TypeInt(i64),
    Kinded(Box<Type>, Box<Type>),
    /// A mutable unification variable; resolved during inference.
    /// Must not appear in any serialized output.
    Unif(u32),
}

impl Type {
    /// `Type` — the kind of ordinary types.
    pub fn kind_type() -> Type {
        Type::Con(QName::unqualified("Type"))
    }

    pub fn fun(from: Type, to: Type) -> Type {
        Type::Fun(Box::new(from), Box::new(to))
    }

    pub fn app(f: Type, arg: Type) -> Type {
        // Normalize `App(App(Con("->"|"Function"), a), b)` into
        // `Type::Fun(a, b)` so value-level function types unify
        // with constructor-applied ones (e.g. instance heads like
        // `Apply ((->) r)` substituted into `f (a -> b) -> f a -> f b`).
        // Catches both the convert-time and substitution-time
        // construction paths — `apply_var_subst` builds App nodes
        // directly via `Type::App(...)` rather than `Type::app`,
        // but every non-substitution entry point funnels through
        // here.
        if let Type::App(inner_f, inner_a) = &f {
            if let Type::Con(qn) = inner_f.as_ref() {
                if qn.name == "->" || qn.name == "Function" {
                    return Type::Fun(Box::new(inner_a.as_ref().clone()), Box::new(arg));
                }
            }
        }
        Type::App(Box::new(f), Box::new(arg))
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Constraint {
    pub class: QName,
    pub args: Vec<Type>,
}

/// A type scheme — forall vars + a monotype body.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Scheme {
    pub vars: Vec<String>,
    pub ty: Type,
}

impl Scheme {
    pub fn mono(ty: Type) -> Self {
        Self { vars: Vec::new(), ty }
    }
}

// ============================================================================
// CST → wire Type
// ============================================================================

/// Mapping from a type-level operator to its canonical type constructor.
///
/// `infixr 6 type Tuple as /\` introduces an entry mapping `/\` (possibly
/// module-qualified) to `QName { module: Some("Data.Tuple"), name: "Tuple" }`.
pub type TypeOpMap = HashMap<(Option<String>, String), QName>;

/// Convert a CST `TypeExpr` into a serializable wire [`Type`].
///
/// Type-level operators are desugared to applications: `a /\ b` becomes
/// `App(App(Con(Tuple), a), b)` when `type_ops` has a mapping for `/\`.
/// Without a mapping the op is preserved using its own name as the
/// constructor — which is wrong semantically but keeps the structural
/// conversion total. Real operator resolution happens in passes that
/// thread the full scope.
pub fn convert_type_expr(ty: &cst::TypeExpr, type_ops: &TypeOpMap) -> Type {
    use cst::TypeExpr as TE;
    match ty {
        TE::Var { name, .. } => Type::Var(resolve(name.value.symbol())),
        TE::Constructor { name, .. } => Type::Con(qname_of_qualified(
            name.module.map(|m| m.symbol()),
            name.name.symbol(),
        )),
        TE::App { constructor, arg, .. } => {
            let f = convert_type_expr(constructor, type_ops);
            let a = convert_type_expr(arg, type_ops);
            // Normalize `(->) x y` (which parses to a 2-step App
            // chain) into the canonical `Type::Fun(x, y)`. Without
            // this, instance heads like `Apply ((->) r)` carry the
            // function type as `App(App(Con("->"), r), arg)` while
            // value-level lambdas use `Fun(...)` — the unifier
            // treats those as distinct shapes and breaks instance
            // matching for `(->) r`-style instances.
            if let Type::App(inner_f, inner_a) = &f {
                if let Type::Con(qn) = inner_f.as_ref() {
                    if qn.name == "->" || qn.name == "Function" {
                        return Type::fun(inner_a.as_ref().clone(), a);
                    }
                }
            }
            Type::app(f, a)
        }
        TE::Function { from, to, .. } => Type::fun(
            convert_type_expr(from, type_ops),
            convert_type_expr(to, type_ops),
        ),
        TE::Forall { vars, ty, .. } => {
            let vs = vars
                .iter()
                .map(|(v, visible, kind)| {
                    (
                        resolve(v.value.symbol()),
                        *visible,
                        kind.as_ref().map(|k| Box::new(convert_type_expr(k, type_ops))),
                    )
                })
                .collect();
            Type::Forall(vs, Box::new(convert_type_expr(ty, type_ops)))
        }
        TE::Constrained { constraints, ty, .. } => {
            let cs = constraints
                .iter()
                .map(|c| Constraint {
                    class: qname_of_qualified(
                        c.class.module.map(|m| m.symbol()),
                        c.class.name.symbol(),
                    ),
                    args: c.args.iter().map(|a| convert_type_expr(a, type_ops)).collect(),
                })
                .collect();
            Type::Constrained(cs, Box::new(convert_type_expr(ty, type_ops)))
        }
        TE::Record { fields, .. } => Type::Record(
            fields
                .iter()
                .map(|f| (resolve(f.label.value.symbol()), convert_type_expr(&f.ty, type_ops)))
                .collect(),
            None,
        ),
        TE::Row { fields, tail, is_record, .. } => {
            let fs: Vec<_> = fields
                .iter()
                .map(|f| (resolve(f.label.value.symbol()), convert_type_expr(&f.ty, type_ops)))
                .collect();
            let t = tail.as_ref().map(|t| Box::new(convert_type_expr(t, type_ops)));
            if *is_record {
                Type::Record(fs, t)
            } else {
                Type::Row(fs, t)
            }
        }
        TE::Parens { ty, .. } => convert_type_expr(ty, type_ops),
        TE::Hole { name, .. } => Type::Hole(resolve(name.symbol())),
        TE::Wildcard { .. } => Type::Wildcard,
        TE::TypeOp { left, op, right, .. } => {
            let module = op.value.module.map(|m| resolve(m.symbol()));
            let name = resolve(op.value.name.symbol());
            let target = type_ops
                .get(&(module.clone(), name.clone()))
                .cloned()
                .unwrap_or(QName { module, name });
            Type::app(
                Type::app(
                    Type::Con(target),
                    convert_type_expr(left, type_ops),
                ),
                convert_type_expr(right, type_ops),
            )
        }
        TE::Kinded { ty, kind, .. } => Type::Kinded(
            Box::new(convert_type_expr(ty, type_ops)),
            Box::new(convert_type_expr(kind, type_ops)),
        ),
        TE::StringLiteral { value, .. } => Type::TypeString(value.clone()),
        TE::IntLiteral { value, .. } => Type::TypeInt(*value),
        // These variants only arise from VTA parsing for as-patterns and
        // aren't meaningful at the type level. Treat as opaque wildcards.
        TE::ArrayPattern { .. } | TE::AsPattern { .. } => Type::Wildcard,
    }
}

// ============================================================================
// helpers
// ============================================================================

fn resolve(sym: crate::interner::Symbol) -> String {
    crate::typecheck_db::util::resolve_symbol(sym)
}

/// Deterministic hash of a [`TypeOpMap`], used by passes that fold this map
/// into their input hash.
pub fn hash_type_ops(type_ops: &TypeOpMap) -> [u8; 32] {
    use crate::typecheck_db::util::hash_opt_str;
    let mut sorted: Vec<(&(Option<String>, String), &QName)> = type_ops.iter().collect();
    sorted.sort_by(|a, b| a.0.cmp(b.0));
    let mut h = blake3::Hasher::new();
    h.update(&(sorted.len() as u32).to_le_bytes());
    for ((mod_opt, op_name), target) in sorted {
        hash_opt_str(&mut h, mod_opt.as_deref());
        h.update(op_name.as_bytes());
        h.update(&[0u8]);
        hash_opt_str(&mut h, target.module.as_deref());
        h.update(target.name.as_bytes());
        h.update(&[0u8]);
    }
    *h.finalize().as_bytes()
}

fn qname_of_qualified(
    module: Option<crate::interner::Symbol>,
    name: crate::interner::Symbol,
) -> QName {
    QName {
        module: module.map(resolve),
        name: resolve(name),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse;

    fn single_sig_ty(src: &str) -> cst::TypeExpr {
        let module = parse(src).unwrap();
        for d in module.decls {
            if let cst::Decl::TypeSignature { ty, .. } = d {
                return ty;
            }
        }
        panic!("no type signature in source");
    }

    #[test]
    fn converts_function_of_prim() {
        let ty = single_sig_ty("module M where\nfoo :: Int -> Boolean\nfoo = undefined\n");
        let ops = TypeOpMap::default();
        let t = convert_type_expr(&ty, &ops);
        assert_eq!(
            t,
            Type::fun(
                Type::Con(QName::unqualified("Int")),
                Type::Con(QName::unqualified("Boolean")),
            )
        );
    }

    #[test]
    fn preserves_forall_and_vars() {
        let ty =
            single_sig_ty("module M where\nfoo :: forall a. a -> a\nfoo x = x\n");
        let t = convert_type_expr(&ty, &TypeOpMap::default());
        match t {
            Type::Forall(vars, body) => {
                assert_eq!(vars.len(), 1);
                assert_eq!(vars[0].0, "a");
                assert_eq!(*body, Type::fun(Type::Var("a".into()), Type::Var("a".into())));
            }
            other => panic!("expected Forall, got {:?}", other),
        }
    }

    #[test]
    fn converts_constrained() {
        let ty = single_sig_ty(
            "module M where\nfoo :: forall a. Eq a => a -> Boolean\nfoo _ = true\n",
        );
        let t = convert_type_expr(&ty, &TypeOpMap::default());
        let body = match t {
            Type::Forall(_, body) => *body,
            _ => panic!("expected outer forall"),
        };
        match body {
            Type::Constrained(cs, inner) => {
                assert_eq!(cs.len(), 1);
                assert_eq!(cs[0].class.name, "Eq");
                assert_eq!(
                    *inner,
                    Type::fun(Type::Var("a".into()), Type::Con(QName::unqualified("Boolean"))),
                );
            }
            other => panic!("expected Constrained, got {:?}", other),
        }
    }

    #[test]
    fn converts_record() {
        let ty = single_sig_ty(
            "module M where\nfoo :: { name :: String, age :: Int }\nfoo = undefined\n",
        );
        let t = convert_type_expr(&ty, &TypeOpMap::default());
        match t {
            Type::Record(fields, tail) => {
                assert!(tail.is_none());
                let names: Vec<_> = fields.iter().map(|(n, _)| n.as_str()).collect();
                assert!(names.contains(&"name") && names.contains(&"age"));
            }
            other => panic!("expected Record, got {:?}", other),
        }
    }
}
