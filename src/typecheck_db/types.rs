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
            // Elide the Prim[.Sub] prefix in display: matches the
            // PureScript reference compiler's convention of showing
            // `Int` not `Prim.Int`, `Maybe` not `Data.Maybe.Maybe`
            // when the type is unambiguous. Diagnostics stay
            // readable; structural equality still uses the full
            // qualified form.
            if m == "Prim" || m.starts_with("Prim.") {
                write!(f, "{}", self.name)
            } else {
                write!(f, "{}.{}", m, self.name)
            }
        } else {
            write!(f, "{}", self.name)
        }
    }
}

/// Like [`QName`] but with a mandatory defining-module qualifier.
///
/// Produced by the name-resolution pass; the `module` field always
/// points at the module that DEFINES the entity, never an intermediate
/// re-exporter. Downstream passes consume `ResolvedQName` instead of
/// `QName` to eliminate the ambient `Option`-handling.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ResolvedQName {
    pub module: String,
    pub name: String,
}

impl ResolvedQName {
    pub fn new(module: impl Into<String>, name: impl Into<String>) -> Self {
        Self { module: module.into(), name: name.into() }
    }

    /// Convert to a legacy [`QName`] with `Some(module)`. Used at
    /// boundaries with code that still operates on the optional-
    /// qualifier representation during the migration.
    pub fn to_qname(&self) -> QName {
        QName {
            module: Some(self.module.clone()),
            name: self.name.clone(),
        }
    }
}

impl fmt::Display for ResolvedQName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}.{}", self.module, self.name)
    }
}

// ---------------------------------------------------------------------------
// Prim helpers — every primitive built-in Type::Con with its defining module
// ---------------------------------------------------------------------------
//
// Prim is split into submodules: `Prim` defines Int/Number/Boolean/etc.;
// `Prim.Boolean` defines True/False; `Prim.Ordering` defines LT/EQ/GT;
// `Prim.Row` / `Prim.RowList` / `Prim.Symbol` / `Prim.TypeError` / `Prim.Coerce`
// / `Prim.Int` define their respective entities. These helpers produce
// `Type::Con` with the correct defining-module qualifier so the resolver-
// driven invariant (every Type::Con carries Some(defining_module)) holds
// throughout the codebase.

macro_rules! prim_helper {
    ($fn:ident, $module:expr, $name:expr) => {
        #[inline]
        pub fn $fn() -> Type {
            Type::Con(QName::qualified($module, $name))
        }
    };
}

// Prim itself (the canonical primitive module).
prim_helper!(prim_int, "Prim", "Int");
prim_helper!(prim_number, "Prim", "Number");
prim_helper!(prim_string, "Prim", "String");
prim_helper!(prim_char, "Prim", "Char");
prim_helper!(prim_boolean, "Prim", "Boolean");
prim_helper!(prim_array, "Prim", "Array");
prim_helper!(prim_record, "Prim", "Record");
prim_helper!(prim_function, "Prim", "Function");
prim_helper!(prim_kind_type, "Prim", "Type");
prim_helper!(prim_constraint, "Prim", "Constraint");
prim_helper!(prim_symbol, "Prim", "Symbol");
prim_helper!(prim_row, "Prim", "Row");
prim_helper!(prim_partial, "Prim", "Partial");
// Note: `IsSymbol` is defined in `Data.Symbol` (compiler-magic class).
// `Prim` exposes it as a fallback for legacy import resolution, but the
// canonical defining module is Data.Symbol — no Prim helper here.

// Prim.Boolean — type-level booleans.
prim_helper!(prim_true, "Prim.Boolean", "True");
prim_helper!(prim_false, "Prim.Boolean", "False");

// Prim.Ordering.
prim_helper!(prim_ordering, "Prim.Ordering", "Ordering");
prim_helper!(prim_lt, "Prim.Ordering", "LT");
prim_helper!(prim_eq, "Prim.Ordering", "EQ");
prim_helper!(prim_gt, "Prim.Ordering", "GT");

// Prim.Row — row-polymorphism classes.
prim_helper!(prim_row_cons, "Prim.Row", "Cons");
prim_helper!(prim_row_union, "Prim.Row", "Union");
prim_helper!(prim_row_nub, "Prim.Row", "Nub");
prim_helper!(prim_row_lacks, "Prim.Row", "Lacks");

// Prim.RowList — row reflection.
prim_helper!(prim_rowlist_cons, "Prim.RowList", "Cons");
prim_helper!(prim_rowlist_nil, "Prim.RowList", "Nil");
prim_helper!(prim_rowlist_rowlist, "Prim.RowList", "RowList");

// Prim.Symbol — type-level string ops.
prim_helper!(prim_symbol_cons, "Prim.Symbol", "Cons");
prim_helper!(prim_symbol_compare, "Prim.Symbol", "Compare");
prim_helper!(prim_symbol_append, "Prim.Symbol", "Append");

// Prim.TypeError — type-level error messages.
prim_helper!(prim_fail, "Prim.TypeError", "Fail");
prim_helper!(prim_warn, "Prim.TypeError", "Warn");
prim_helper!(prim_above, "Prim.TypeError", "Above");
prim_helper!(prim_beside, "Prim.TypeError", "Beside");
prim_helper!(prim_quote, "Prim.TypeError", "Quote");
prim_helper!(prim_quote_label, "Prim.TypeError", "QuoteLabel");
prim_helper!(prim_text, "Prim.TypeError", "Text");
prim_helper!(prim_doc, "Prim.TypeError", "Doc");

// Prim.Coerce.
prim_helper!(prim_coercible, "Prim.Coerce", "Coercible");

// Prim.Int — type-level integer arithmetic.
prim_helper!(prim_int_add, "Prim.Int", "Add");
prim_helper!(prim_int_mul, "Prim.Int", "Mul");
prim_helper!(prim_int_compare, "Prim.Int", "Compare");
prim_helper!(prim_int_to_string, "Prim.Int", "ToString");

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
        prim_kind_type()
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

/// Map from a type-alias `(Option<module>, name)` to its
/// `(type_vars, body)`. Built once per module check (local
/// aliases + every imported module's aliases) and passed to
/// `expand_aliases` so signatures, constructor fields, instance
/// heads, and the like all get their aliases unfolded before
/// unification compares them.
///
/// The qualifier-aware key distinguishes aliases from different
/// modules that happen to share a simple name (e.g.
/// `Control.Monad.State.State` and a locally-imported
/// `Marionette.Types.State` newtype — the alias for `State`
/// from `Control.Monad.State` is registered ONLY under
/// `(Some("Control.Monad.State"), "State")`, never under
/// `(None, "State")`, so it doesn't silently expand at use-sites
/// that expect the newtype).
///
/// `expand_once` looks up the qualified form first (using the
/// `Type::Con`'s module qualifier), then falls back to the
/// unqualified form when the user explicitly imported the alias.
pub type AliasMap = HashMap<(Option<String>, String), (Vec<String>, Type)>;

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

/// True when `ty` structurally contains `Con(name)` (module
/// qualifier ignored). Used by `expand_once` to detect
/// self-referential aliases — an alias whose body mentions
/// its own name would expand indefinitely (exponentially for
/// branching rows like `Style.Evaluated`).
fn body_mentions_name(ty: &Type, name: &str) -> bool {
    match ty {
        Type::Con(qn) => qn.name == name,
        Type::App(f, a) | Type::Fun(f, a) => {
            body_mentions_name(f, name) || body_mentions_name(a, name)
        }
        Type::Row(fs, tail) | Type::Record(fs, tail) => {
            fs.iter().any(|(_, t)| body_mentions_name(t, name))
                || tail
                    .as_ref()
                    .map_or(false, |t| body_mentions_name(t, name))
        }
        Type::Forall(_, b) => body_mentions_name(b, name),
        Type::Kinded(t, k) => {
            body_mentions_name(t, name) || body_mentions_name(k, name)
        }
        Type::Constrained(cs, b) => {
            cs.iter()
                .any(|c| c.args.iter().any(|a| body_mentions_name(a, name)))
                || body_mentions_name(b, name)
        }
        _ => false,
    }
}

/// Eta-reduce `body` by stripping trailing `App(_, Var(v))` layers
/// matching the `missing` vars in order. Returns the stripped body
/// only when:
///   * each trailing App's arg is exactly `Var(missing[k])`, AND
///   * after stripping, none of the missing vars appear anywhere
///     in the remaining body (otherwise eta-reduction is unsound).
///
/// Used for under-saturated alias expansion (`type Tree a = Cofree
/// Array a` applied as just `Tree`).
fn try_eta_reduce(body: &Type, missing: &[String]) -> Option<Type> {
    let mut current = body.clone();
    for v in missing.iter().rev() {
        match current {
            Type::App(inner, arg) => match arg.as_ref() {
                Type::Var(n) if n == v => {
                    current = (*inner).clone();
                }
                _ => return None,
            },
            _ => return None,
        }
    }
    for v in missing {
        if type_mentions_var(&current, v) {
            return None;
        }
    }
    Some(current)
}

fn type_mentions_var(ty: &Type, var: &str) -> bool {
    match ty {
        Type::Var(n) => n == var,
        Type::App(f, a) | Type::Fun(f, a) => {
            type_mentions_var(f, var) || type_mentions_var(a, var)
        }
        Type::Row(fs, tail) | Type::Record(fs, tail) => {
            fs.iter().any(|(_, t)| type_mentions_var(t, var))
                || tail.as_ref().map_or(false, |t| type_mentions_var(t, var))
        }
        Type::Forall(vs, b) => {
            !vs.iter().any(|(n, _, _)| n == var) && type_mentions_var(b, var)
        }
        Type::Kinded(t, k) => {
            type_mentions_var(t, var) || type_mentions_var(k, var)
        }
        Type::Constrained(cs, b) => {
            cs.iter()
                .any(|c| c.args.iter().any(|a| type_mentions_var(a, var)))
                || type_mentions_var(b, var)
        }
        _ => false,
    }
}

/// True when `ty` structurally contains `Con(QName { module, name
/// })` — both fields must match. Used by `expand_once` to detect
/// self-referential aliases without false positives across modules
/// (e.g. `type Result = Other.Result` is not self-referential when
/// the alias's qualified key is `(Some("W"), "Result")`).
fn body_mentions_qname(ty: &Type, module: &Option<String>, name: &str) -> bool {
    match ty {
        Type::Con(qn) => &qn.module == module && qn.name == name,
        Type::App(f, a) | Type::Fun(f, a) => {
            body_mentions_qname(f, module, name)
                || body_mentions_qname(a, module, name)
        }
        Type::Row(fs, tail) | Type::Record(fs, tail) => {
            fs.iter().any(|(_, t)| body_mentions_qname(t, module, name))
                || tail
                    .as_ref()
                    .map_or(false, |t| body_mentions_qname(t, module, name))
        }
        Type::Forall(_, b) => body_mentions_qname(b, module, name),
        Type::Kinded(t, k) => {
            body_mentions_qname(t, module, name)
                || body_mentions_qname(k, module, name)
        }
        Type::Constrained(cs, b) => {
            cs.iter().any(|c| {
                c.args.iter().any(|a| body_mentions_qname(a, module, name))
            }) || body_mentions_qname(b, module, name)
        }
        _ => false,
    }
}

fn expand_once(ty: &Type, aliases: &AliasMap) -> Type {
    // Collect the Con head + its App spine so we can try to
    // match the whole applied form against an alias. Anything
    // that isn't head-shaped (e.g. Fun, Forall, Record) or that
    // doesn't have a matching alias falls through to a
    // structural recurse.
    let spine = collect_app_spine(ty);
    if let Some((Type::Con(qn), args)) = spine {
        // Qualifier-aware lookup. When the type carries a module
        // qualifier (resolver-rewritten), look up the exact
        // `(Some(module), name)` key — DO NOT fall back to the
        // unqualified entry. That would misroute a
        // `Type::Con(Some("Marionette.Types"), "State")` (a local
        // newtype, no alias entry) to the imported
        // `Control.Monad.State.State` alias's `(None, "State")`
        // entry, expanding the newtype as if it were the
        // transformers alias.
        //
        // Only the unqualified case (`module: None`, surviving
        // some legacy synthesizer that didn't qualify) falls
        // through to the `(None, name)` entry.
        let entry = if qn.module.is_some() {
            aliases.get(&(qn.module.clone(), qn.name.clone()))
        } else {
            aliases.get(&(None, qn.name.clone()))
        };
        if let Some((vars, body)) = entry {
            // Skip self-referential aliases: comparing both module
            // and name avoids the cross-module false positive
            // (`type Result = M.Result` in module W is not
            // self-referential — body Con has module Some("M")).
            if !body_mentions_qname(body, &qn.module, &qn.name) {
                let n_args = args.len();
                let n_vars = vars.len();
                if n_vars == n_args {
                    // Saturated.
                    let mut subst: std::collections::HashMap<String, Type> =
                        std::collections::HashMap::with_capacity(n_vars);
                    for (v, a) in vars.iter().zip(args.iter()) {
                        subst.insert(v.clone(), expand_once(a, aliases));
                    }
                    return crate::typecheck_db::generalize::apply_var_subst(
                        body, &subst,
                    );
                } else if n_args > n_vars {
                    // Over-saturated: substitute, then re-apply
                    // leftover args (`type R = M.R` as `R a` →
                    // `M.R a`).
                    let mut subst: std::collections::HashMap<String, Type> =
                        std::collections::HashMap::with_capacity(n_vars);
                    for (v, a) in vars.iter().zip(args.iter()) {
                        subst.insert(v.clone(), expand_once(a, aliases));
                    }
                    let expanded =
                        crate::typecheck_db::generalize::apply_var_subst(
                            body, &subst,
                        );
                    return args[n_vars..].iter().fold(expanded, |acc, a| {
                        Type::app(acc, expand_once(a, aliases))
                    });
                } else if let Some(eta_body) =
                    try_eta_reduce(body, &vars[n_args..])
                {
                    // Under-saturated: eta-reduce when the missing
                    // vars sit at the trailing spine of the body
                    // and nowhere else. `type Tree a = Cofree Array
                    // a` used as just `Tree` (kind `Type -> Type`)
                    // reduces to `Cofree Array`.
                    let mut subst: std::collections::HashMap<String, Type> =
                        std::collections::HashMap::with_capacity(n_args);
                    for (v, a) in vars[..n_args].iter().zip(args.iter()) {
                        subst.insert(v.clone(), expand_once(a, aliases));
                    }
                    return crate::typecheck_db::generalize::apply_var_subst(
                        &eta_body, &subst,
                    );
                }
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
/// True if a (post-conversion) `Type` contains a `Type::Hole`
/// anywhere. Used by `env::lookup_qualified` to bypass schemes
/// whose body still carries a user-written `?h` — those schemes
/// only become useful AFTER the sig-pin path rewrites the holes
/// to fresh unifs, so we don't want them returned by recursive-
/// reference lookups during body inference.
pub fn type_contains_hole(ty: &Type) -> bool {
    match ty {
        Type::Hole(_) => true,
        Type::App(f, a) => type_contains_hole(f) || type_contains_hole(a),
        Type::Fun(a, b) => type_contains_hole(a) || type_contains_hole(b),
        Type::Forall(_, body) => type_contains_hole(body),
        Type::Constrained(cs, body) => {
            cs.iter().any(|c| c.args.iter().any(type_contains_hole)) || type_contains_hole(body)
        }
        Type::Record(fields, tail) => {
            fields.iter().any(|(_, t)| type_contains_hole(t))
                || tail.as_deref().map_or(false, type_contains_hole)
        }
        Type::Row(fields, tail) => {
            fields.iter().any(|(_, t)| type_contains_hole(t))
                || tail.as_deref().map_or(false, type_contains_hole)
        }
        Type::Kinded(t, k) => type_contains_hole(t) || type_contains_hole(k),
        Type::Var(_)
        | Type::Con(_)
        | Type::Unif(_)
        | Type::Skolem(_)
        | Type::TypeString(_)
        | Type::TypeInt(_)
        | Type::Wildcard => false,
    }
}

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
