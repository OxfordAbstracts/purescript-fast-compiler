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

impl Type {
    /// Format with explicit precedence context.
    ///
    /// Precedence levels (match PureScript notation):
    ///   0 = outermost — no wrapping needed for `->` or App
    ///   1 = left of `->` — wrap `->` in parens, App is fine
    ///   2 = argument of App — wrap both `->` and App in parens
    fn fmt_prec(&self, f: &mut fmt::Formatter<'_>, prec: u8) -> fmt::Result {
        match self {
            Type::Var(n) => write!(f, "{}", n),
            Type::Con(q) => write!(f, "{}", q),
            Type::App(g, a) => {
                if prec > 1 {
                    write!(f, "(")?;
                    g.fmt_prec(f, 1)?;
                    write!(f, " ")?;
                    a.fmt_prec(f, 2)?;
                    write!(f, ")")
                } else {
                    g.fmt_prec(f, 1)?;
                    write!(f, " ")?;
                    a.fmt_prec(f, 2)
                }
            }
            Type::Fun(a, b) => {
                if prec > 0 {
                    write!(f, "(")?;
                    a.fmt_prec(f, 1)?;
                    write!(f, " -> ")?;
                    b.fmt_prec(f, 0)?;
                    write!(f, ")")
                } else {
                    a.fmt_prec(f, 1)?;
                    write!(f, " -> ")?;
                    b.fmt_prec(f, 0)
                }
            }
            Type::Forall(vars, body) => {
                write!(f, "forall")?;
                for (n, _, _) in vars {
                    write!(f, " {}", n)?;
                }
                write!(f, ". ")?;
                body.fmt_prec(f, 0)
            }
            Type::Constrained(cs, body) => {
                let do_parens = prec > 0;
                if do_parens { write!(f, "(")?; }
                for (i, c) in cs.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", c.class)?;
                    for a in &c.args {
                        write!(f, " ")?;
                        a.fmt_prec(f, 2)?;
                    }
                }
                write!(f, " => ")?;
                body.fmt_prec(f, 0)?;
                if do_parens { write!(f, ")")?; }
                Ok(())
            }
            Type::Record(fields, tail) => {
                write!(f, "{{ ")?;
                for (i, (l, t)) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{} :: ", l)?;
                    t.fmt_prec(f, 0)?;
                }
                if let Some(t) = tail {
                    write!(f, " | ")?;
                    t.fmt_prec(f, 0)?;
                }
                write!(f, " }}")
            }
            Type::Row(fields, tail) => {
                write!(f, "(")?;
                for (i, (l, t)) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{} :: ", l)?;
                    t.fmt_prec(f, 0)?;
                }
                if let Some(t) = tail {
                    write!(f, " | ")?;
                    t.fmt_prec(f, 0)?;
                }
                write!(f, ")")
            }
            Type::Hole(n) => write!(f, "?{}", n),
            Type::Wildcard => write!(f, "_"),
            Type::TypeString(s) => write!(f, "\"{}\"", s),
            Type::TypeInt(n) => write!(f, "{}", n),
            Type::Kinded(t, k) => write!(f, "({} :: {})", t, k),
            Type::Unif(id) => write!(f, "?u{}", id),
            Type::Skolem(id) => write!(f, "!s{}", id),
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt_prec(f, 0)
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
    /// A rigid skolem variable introduced when checking against a
    /// `Forall`. Two skolems are equal iff their ids match; a
    /// skolem never unifies with anything else. Used to enforce
    /// rank-2+ polymorphism: in `test :: (forall a. a -> a) ->
    /// Number`, checking `\\n -> n + 1` against the argument type
    /// introduces a skolem for `a`, then `+` demands `Semiring
    /// skolem_a`, which has no instance — the correct rejection.
    /// Must not appear in any serialized output.
    Skolem(u32),
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

/// Map from a type-alias name to its `(type_vars, body)`. Built
/// once per module check (local aliases + every imported
/// module's aliases) and passed to `expand_aliases` so
/// signatures, constructor fields, instance heads, and the like
/// all get their aliases unfolded before unification compares
/// them. Without this, unifying `SynString` (an alias for
/// `String`) against `String` fails as a `Mismatch`.
pub type AliasMap = HashMap<String, (Vec<String>, Type)>;

/// Walk `ty` and replace every `Type::Con(name)` / applied
/// `App(Con(name), ...)` whose simple name matches an alias
/// with the alias body, substituting each type argument for the
/// corresponding alias variable. Runs to a fixed point to
/// handle nested aliases (`type A = B; type B = Int`). Bare
/// `Type::Con(alias)` with no application only expands when the
/// alias itself has no parameters.
pub fn expand_aliases(ty: Type, aliases: &AliasMap) -> Type {
    if aliases.is_empty() {
        return ty;
    }
    // Fixed-point guard against ill-formed recursive aliases —
    // give up after `MAX_EXPANSIONS` so a broken user alias
    // can't hang the typechecker. 64 is generous; most real
    // alias chains are 1–3 deep.
    const MAX_EXPANSIONS: usize = 64;
    let mut current = ty;
    for _ in 0..MAX_EXPANSIONS {
        let expanded = expand_once(&current, aliases);
        if expanded == current {
            return expanded;
        }
        current = expanded;
    }
    current
}

fn expand_once(ty: &Type, aliases: &AliasMap) -> Type {
    // Collect the Con head + its App spine so we can try to
    // match the whole applied form against an alias. Anything
    // that isn't head-shaped (e.g. Fun, Forall, Record) or that
    // doesn't have a matching alias falls through to a
    // structural recurse.
    let spine = collect_app_spine(ty);
    if let Some((Type::Con(qn), args)) = spine {
        if let Some((vars, body)) = aliases.get(&qn.name) {
            // Only expand saturated applications (vars.len() ==
            // args.len()) for now — partial aliases need the
            // leftover args re-applied to the expanded body and
            // that interacts badly with some of our existing
            // fixtures. Saturated covers the overwhelming common
            // case (`type SynString = String`, `type Fn a = a ->
            // a`).
            if vars.len() == args.len() {
                let mut subst: std::collections::HashMap<String, Type> =
                    std::collections::HashMap::with_capacity(vars.len());
                for (v, a) in vars.iter().zip(args.iter()) {
                    subst.insert(v.clone(), expand_once(a, aliases));
                }
                return crate::typecheck_db::generalize::apply_var_subst(body, &subst);
            }
        }
    }
    // No alias match — walk children, expand each subterm once.
    match ty {
        Type::App(f, a) => Type::app(expand_once(f, aliases), expand_once(a, aliases)),
        Type::Fun(a, b) => Type::fun(expand_once(a, aliases), expand_once(b, aliases)),
        Type::Forall(vars, body) => {
            Type::Forall(vars.clone(), Box::new(expand_once(body, aliases)))
        }
        Type::Constrained(cs, body) => {
            let cs = cs
                .iter()
                .map(|c| Constraint {
                    class: c.class.clone(),
                    args: c.args.iter().map(|x| expand_once(x, aliases)).collect(),
                })
                .collect();
            Type::Constrained(cs, Box::new(expand_once(body, aliases)))
        }
        Type::Record(fs, tail) => Type::Record(
            fs.iter()
                .map(|(l, t)| (l.clone(), expand_once(t, aliases)))
                .collect(),
            tail.as_ref().map(|t| Box::new(expand_once(t, aliases))),
        ),
        Type::Row(fs, tail) => Type::Row(
            fs.iter()
                .map(|(l, t)| (l.clone(), expand_once(t, aliases)))
                .collect(),
            tail.as_ref().map(|t| Box::new(expand_once(t, aliases))),
        ),
        Type::Kinded(t, k) => Type::Kinded(
            Box::new(expand_once(t, aliases)),
            Box::new(expand_once(k, aliases)),
        ),
        other => other.clone(),
    }
}

/// Flatten an `App` spine: `App(App(f, a), b) → (f, [a, b])`.
/// Only returns the spine when the head is reachable through
/// `Type::App` nests; stops at anything else.
fn collect_app_spine(ty: &Type) -> Option<(Type, Vec<Type>)> {
    let mut args: Vec<Type> = Vec::new();
    let mut cursor = ty.clone();
    loop {
        match cursor {
            Type::App(f, a) => {
                args.push(*a);
                cursor = *f;
            }
            other => {
                if args.is_empty() {
                    return Some((other, Vec::new()));
                }
                args.reverse();
                return Some((other, args));
            }
        }
    }
}

/// Convert a CST `TypeExpr` into a serializable wire [`Type`].
///
/// Type-level operators are desugared to applications: `a /\ b` becomes
/// `App(App(Con(Tuple), a), b)` when `type_ops` has a mapping for `/\`.
/// Without a mapping the op is preserved using its own name as the
/// constructor — which is wrong semantically but keeps the structural
/// conversion total. Real operator resolution happens in passes that
/// thread the full scope.
/// Walk a TypeExpr collecting every TE::Hole site as
/// `(span, hole_name)` in source order. Used by inference paths to
/// allocate unif vars + emit `HoleDiagnostic`s for type-level holes.
pub fn collect_type_holes(
    ty: &cst::TypeExpr,
    out: &mut Vec<(crate::span::Span, String)>,
) {
    use cst::TypeExpr as TE;
    match ty {
        TE::Hole { span, name } => {
            out.push((*span, resolve(name.symbol())));
        }
        TE::Var { .. }
        | TE::Constructor { .. }
        | TE::Wildcard { .. }
        | TE::StringLiteral { .. }
        | TE::IntLiteral { .. } => {}
        TE::App { constructor, arg, .. } => {
            collect_type_holes(constructor, out);
            collect_type_holes(arg, out);
        }
        TE::Function { from, to, .. } => {
            collect_type_holes(from, out);
            collect_type_holes(to, out);
        }
        TE::Forall { vars, ty, .. } => {
            for (_, _, k) in vars {
                if let Some(k) = k {
                    collect_type_holes(k, out);
                }
            }
            collect_type_holes(ty, out);
        }
        TE::Constrained { constraints, ty, .. } => {
            for c in constraints {
                for a in &c.args {
                    collect_type_holes(a, out);
                }
            }
            collect_type_holes(ty, out);
        }
        TE::Record { fields, .. } => {
            for f in fields {
                collect_type_holes(&f.ty, out);
            }
        }
        TE::Row { fields, tail, .. } => {
            for f in fields {
                collect_type_holes(&f.ty, out);
            }
            if let Some(t) = tail {
                collect_type_holes(t, out);
            }
        }
        TE::Parens { ty, .. } => collect_type_holes(ty, out),
        TE::TypeOp { left, right, .. } => {
            collect_type_holes(left, out);
            collect_type_holes(right, out);
        }
        TE::Kinded { ty, kind, .. } => {
            collect_type_holes(ty, out);
            collect_type_holes(kind, out);
        }
        TE::ArrayPattern { elements, .. } => {
            for e in elements {
                collect_type_holes(e, out);
            }
        }
        TE::AsPattern { ty, .. } => collect_type_holes(ty, out),
    }
}

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
