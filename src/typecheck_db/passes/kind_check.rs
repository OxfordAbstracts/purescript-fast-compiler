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
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PrimKind {
    Type,
    Symbol,
    Int,
    Boolean,
    Constraint,
    /// Some other (e.g. `Row k`, polykinded `k`) — don't compare.
    Other,
}

#[derive(Debug, Clone, Copy)]
struct ParamKind {
    /// Number of arrows the param expects. None = no kind annotation
    /// (treat as wildcard).
    arrows: Option<usize>,
    /// Primitive kind tag of the output (after stripping arrows).
    /// None when no annotation is available.
    prim: Option<PrimKind>,
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
            .map(|(v, opt)| {
                let arrows = match (opt.as_deref(), default_to_type) {
                    (Some(te), _) => Some(arrow_count(te)),
                    (None, true) if hkt_vars.contains(v) => None,
                    (None, true) if poly_vars.contains(v) => None,
                    (None, true) => Some(0),
                    (None, false) => None,
                };
                // prim-kind tag: only trust EXPLICIT annotations.
                // Default-to-Type would false-positive on locally-
                // defined polykinded types (`data Proxy k =
                // Proxy`) used at Symbol / Int positions.
                let prim = match opt.as_deref() {
                    Some(te) => prim_kind_of(te),
                    None => None,
                };
                ParamKind { arrows, prim }
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
    let kind_sig_groups = build_kind_sig_groups(module);
    let kind_sig_param_arrows = build_kind_sig_param_arrows(module);
    let mut errors: Vec<KindError> = Vec::new();
    let mut ctx = Ctx {
        arity_env: &arity_env,
        class_env: &class_env,
        param_kinds: &param_kinds,
        kind_sig_groups: &kind_sig_groups,
        kind_sig_param_arrows: &kind_sig_param_arrows,
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
            cst::Decl::Instance { constraints, class_name, types, members, span, .. } => {
                for c in constraints {
                    ctx.check_constraint(c);
                }
                for t in types {
                    ctx.check_type(t);
                }
                ctx.check_known_hkt_class_instance(class_name, types, *span);
                ctx.check_instance_head_kind_groups(class_name, types);
                for m in members {
                    if let cst::Decl::TypeSignature { ty, .. } = m {
                        ctx.check_type(ty);
                    }
                }
            }
            cst::Decl::Derive { constraints, class_name, types, span, .. } => {
                for c in constraints {
                    ctx.check_constraint(c);
                }
                for t in types {
                    ctx.check_type(t);
                }
                ctx.check_known_hkt_class_instance(class_name, types, *span);
                ctx.check_instance_head_kind_groups(class_name, types);
            }
            cst::Decl::Value { binders, guarded, where_clause, .. } => {
                // Walk every type-annotation inside the body /
                // binders / where-clause so kind-arity / prim-kind
                // checks fire on `(x :: F)` or `(expr :: F a)`.
                for b in binders {
                    ctx.check_binder_types(b);
                }
                ctx.check_guarded_types(guarded);
                for w in where_clause {
                    ctx.check_let_binding_types(w);
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
    /// For each type with a standalone polykinded sig (`data X ::
    /// forall k. k -> k -> Type`), the i-th entry is the
    /// forall-var name that the i-th arg position binds. None
    /// means the position isn't a Var (concrete kind).
    kind_sig_groups: &'a HashMap<Symbol, Vec<Option<Symbol>>>,
    /// For each type with a standalone polykind sig, the
    /// per-arg-position arrow count (extracted from each function
    /// position's kind in the sig).
    kind_sig_param_arrows: &'a HashMap<Symbol, Vec<usize>>,
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
                // Standalone-polykind group check: `data X ::
                // forall k. k -> k -> Type; X Int "foo"` — both
                // args bound to `k`, must share prim kind.
                if let Some(groups) = self.kind_sig_groups.get(&sym) {
                    use std::collections::HashMap as Map;
                    let mut by_var: Map<Symbol, Vec<(usize, PrimKind)>> =
                        Map::new();
                    for (i, arg) in args.iter().enumerate() {
                        if let Some(Some(var)) = groups.get(i) {
                            if let Some(pk) = arg_prim_kind(arg) {
                                if pk != PrimKind::Other {
                                    by_var.entry(*var).or_default().push((i, pk));
                                }
                            }
                        }
                    }
                    for (_var, group_args) in &by_var {
                        if group_args.len() < 2 {
                            continue;
                        }
                        let first = group_args[0].1;
                        for (i, pk) in &group_args[1..] {
                            if *pk != first {
                                self.errors.push(KindError {
                                    span: args[*i].span(),
                                    kind: KindErrorKind::KindsDoNotUnify {
                                        head: resolve(sym),
                                        expected: 0,
                                        got: 0,
                                    },
                                });
                                break;
                            }
                        }
                    }
                }
                if let Some(params) = self.param_kinds.get(&sym) {
                    // Don't enforce arg-position kind checks for
                    // expressions inside Decl::Value bodies when
                    // the param has NO explicit annotation —
                    // locally-defined polykinded types like
                    // `data Proxy a = Proxy` are commonly used
                    // at non-Type kinds in expression-level
                    // annotations.
                    for (i, arg) in args.iter().enumerate() {
                        if let Some(p) = params.get(i) {
                            // Restricted arrow check: only fire
                            // when the param has a Some(prim) tag
                            // — meaning the kind was explicitly
                            // annotated. Without that the
                            // default-to-Type can false-positive
                            // on polykinded vars.
                            if p.prim.is_some() {
                                if let Some(expected_arrows) = p.arrows {
                                    if let Some(actual_arrows) =
                                        self.infer_arg_arrows(arg)
                                    {
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
                            if let Some(expected_prim) = p.prim {
                                if expected_prim != PrimKind::Other {
                                    if let Some(actual_prim) = arg_prim_kind(arg)
                                    {
                                        if actual_prim != PrimKind::Other
                                            && actual_prim != expected_prim
                                        {
                                            self.errors.push(KindError {
                                                span: arg.span(),
                                                kind: KindErrorKind::KindsDoNotUnify {
                                                    head: resolve(sym),
                                                    expected: 0,
                                                    got: 0,
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

    /// Check `instance C T` / `derive instance C T` against a small
    /// table of well-known stdlib classes whose type-parameter must be
    /// of a known kind (`Functor :: (Type → Type) → Constraint`,
    /// `Bifunctor :: (Type → Type → Type) → Constraint`, etc.). Catches
    /// `derive instance Foldable Foo` where `Foo :: Type` doesn't have
    /// the HKT shape Foldable expects.
    ///
    /// Restricted to a hardcoded list because we don't reliably track
    /// imported-class param-kinds; the class-decl param_kinds builder
    /// defaults too aggressively and would false-positive on classes
    /// whose only var-uses are in superclasses (`class (Bind m,
    /// Applicative m) <= Monad m`).
    fn check_known_hkt_class_instance(
        &mut self,
        class_name: &crate::names::Qualified<crate::names::ClassName>,
        types: &[cst::TypeExpr],
        span: Span,
    ) {
        let class_str =
            crate::interner::resolve(class_name.name.symbol()).unwrap_or_default();
        let expected_arrows = match class_str.as_str() {
            "Functor" | "Foldable" | "Traversable" | "Apply" | "Applicative"
            | "Bind" | "Monad" | "Alt" | "Plus" | "Alternative"
            | "MonadPlus" | "MonadZero" | "MonadEffect" | "Extend"
            | "Comonad" | "Contravariant" | "Invariant" | "Filterable" => 1,
            "Bifunctor" | "Profunctor" | "Bifoldable" | "Bitraversable" => 2,
            _ => return,
        };
        // Single-arg classes: check the first (only) type arg.
        if let Some(arg) = types.first() {
            let actual = self.infer_arg_arrows(arg);
            if let Some(actual_arrows) = actual {
                if actual_arrows != expected_arrows {
                    self.errors.push(KindError {
                        span,
                        kind: KindErrorKind::KindsDoNotUnify {
                            head: class_str.clone(),
                            expected: expected_arrows,
                            got: actual_arrows,
                        },
                    });
                    return;
                }
            }
            // Beyond top-level arrows: when the head type has a
            // standalone polykind sig (`data Foo :: (Type -> Type)
            // -> Type`), check that its FIRST PARAM's kind matches
            // what the class expects (Type for Functor/etc.).
            // Catches `derive instance Foldable Foo` where Foo's
            // first param is itself a `Type -> Type`.
            if expected_arrows == 1 {
                if let cst::TypeExpr::Constructor { name, .. } = arg {
                    if name.module.is_none() {
                        let sym = name.name.symbol();
                        if let Some(first_param_arrows) =
                            self.kind_sig_first_param_arrows(sym)
                        {
                            if first_param_arrows != 0 {
                                self.errors.push(KindError {
                                    span,
                                    kind: KindErrorKind::KindsDoNotUnify {
                                        head: class_str,
                                        expected: 0,
                                        got: first_param_arrows,
                                    },
                                });
                            }
                        }
                    }
                }
            }
        }
    }

    /// For a type with a standalone polykind sig, return the
    /// arrow count of its FIRST param's kind. E.g. for
    /// `data Foo :: (Type -> Type) -> Type`, returns Some(1)
    /// (the first param is `Type -> Type`, which has 1 arrow).
    /// `None` when no kind sig is available, or its shape isn't
    /// the expected forall*. arrow chain.
    fn kind_sig_first_param_arrows(&self, sym: Symbol) -> Option<usize> {
        self.kind_sig_param_arrows.get(&sym)?.first().copied()
    }

    /// Constraint arity check: a class declared with N type params
    /// must be applied with exactly N arguments.
    fn check_binder_types(&mut self, b: &cst::Binder) {
        match b {
            cst::Binder::Typed { binder, ty, .. } => {
                self.check_type(ty);
                self.check_binder_types(binder);
            }
            cst::Binder::Parens { binder, .. }
            | cst::Binder::As { binder, .. } => self.check_binder_types(binder),
            cst::Binder::Constructor { args, .. } => {
                for a in args {
                    self.check_binder_types(a);
                }
            }
            cst::Binder::Record { fields, .. } => {
                for f in fields {
                    if let Some(b) = &f.binder {
                        self.check_binder_types(b);
                    }
                }
            }
            cst::Binder::Array { elements, .. } => {
                for e in elements {
                    self.check_binder_types(e);
                }
            }
            cst::Binder::Op { left, right, .. } => {
                self.check_binder_types(left);
                self.check_binder_types(right);
            }
            _ => {}
        }
    }

    fn check_guarded_types(&mut self, g: &cst::GuardedExpr) {
        match g {
            cst::GuardedExpr::Unconditional(e) => self.check_expr_types(e),
            cst::GuardedExpr::Guarded(guards) => {
                for gd in guards {
                    for p in &gd.patterns {
                        match p {
                            cst::GuardPattern::Boolean(e) => self.check_expr_types(e),
                            cst::GuardPattern::Pattern(b, e) => {
                                self.check_binder_types(b);
                                self.check_expr_types(e);
                            }
                        }
                    }
                    self.check_expr_types(&gd.expr);
                }
            }
        }
    }

    fn check_let_binding_types(&mut self, lb: &cst::LetBinding) {
        match lb {
            cst::LetBinding::Value { binder, expr, .. } => {
                self.check_binder_types(binder);
                self.check_expr_types(expr);
            }
            cst::LetBinding::Signature { ty, .. } => self.check_type(ty),
        }
    }

    fn check_expr_types(&mut self, e: &cst::Expr) {
        match e {
            cst::Expr::TypeAnnotation { expr, ty, .. } => {
                self.check_type(ty);
                self.check_expr_types(expr);
            }
            cst::Expr::VisibleTypeApp { func, ty, .. } => {
                self.check_type(ty);
                self.check_expr_types(func);
            }
            cst::Expr::App { func, arg, .. } => {
                self.check_expr_types(func);
                self.check_expr_types(arg);
            }
            cst::Expr::Lambda { binders, body, .. } => {
                for b in binders {
                    self.check_binder_types(b);
                }
                self.check_expr_types(body);
            }
            cst::Expr::Op { left, right, .. } => {
                self.check_expr_types(left);
                self.check_expr_types(right);
            }
            cst::Expr::If { cond, then_expr, else_expr, .. } => {
                self.check_expr_types(cond);
                self.check_expr_types(then_expr);
                self.check_expr_types(else_expr);
            }
            cst::Expr::Case { exprs, alts, .. } => {
                for e in exprs {
                    self.check_expr_types(e);
                }
                for alt in alts {
                    for b in &alt.binders {
                        self.check_binder_types(b);
                    }
                    self.check_guarded_types(&alt.result);
                }
            }
            cst::Expr::Let { bindings, body, .. } => {
                for lb in bindings {
                    self.check_let_binding_types(lb);
                }
                self.check_expr_types(body);
            }
            cst::Expr::Do { statements, .. } => {
                for s in statements {
                    self.check_do_types(s);
                }
            }
            cst::Expr::Ado { statements, result, .. } => {
                for s in statements {
                    self.check_do_types(s);
                }
                self.check_expr_types(result);
            }
            cst::Expr::Record { fields, .. } => {
                for f in fields {
                    if let Some(v) = &f.value {
                        self.check_expr_types(v);
                    }
                }
            }
            cst::Expr::Array { elements, .. } => {
                for el in elements {
                    self.check_expr_types(el);
                }
            }
            cst::Expr::RecordUpdate { expr, updates, .. } => {
                self.check_expr_types(expr);
                for u in updates {
                    self.check_expr_types(&u.value);
                }
            }
            cst::Expr::Parens { expr, .. } | cst::Expr::Negate { expr, .. } => {
                self.check_expr_types(expr);
            }
            _ => {}
        }
    }

    fn check_do_types(&mut self, s: &cst::DoStatement) {
        match s {
            cst::DoStatement::Bind { binder, expr, .. } => {
                self.check_binder_types(binder);
                self.check_expr_types(expr);
            }
            cst::DoStatement::Discard { expr, .. } => {
                self.check_expr_types(expr);
            }
            cst::DoStatement::Let { bindings, .. } => {
                for lb in bindings {
                    self.check_let_binding_types(lb);
                }
            }
        }
    }

    fn check_instance_head_kind_groups(
        &mut self,
        class_name: &crate::names::Qualified<crate::names::ClassName>,
        types: &[cst::TypeExpr],
    ) {
        if class_name.module.is_some() {
            return;
        }
        let sym = class_name.name.symbol();
        let groups = match self.kind_sig_groups.get(&sym) {
            Some(g) => g.clone(),
            None => return,
        };
        use std::collections::HashMap as Map;
        let mut by_var: Map<Symbol, Vec<(usize, PrimKind)>> = Map::new();
        for (i, arg) in types.iter().enumerate() {
            if let Some(Some(var)) = groups.get(i) {
                if let Some(pk) = arg_prim_kind(arg) {
                    if pk != PrimKind::Other {
                        by_var.entry(*var).or_default().push((i, pk));
                    }
                }
            }
        }
        for (_var, group_args) in &by_var {
            if group_args.len() < 2 {
                continue;
            }
            let first = group_args[0].1;
            for (i, pk) in &group_args[1..] {
                if *pk != first {
                    self.errors.push(KindError {
                        span: types[*i].span(),
                        kind: KindErrorKind::KindsDoNotUnify {
                            head: resolve(sym),
                            expected: 0,
                            got: 0,
                        },
                    });
                    break;
                }
            }
        }
    }

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
/// Walk every Data/Newtype/TypeAlias/Class declaration with a
/// `kind_type: Some(...)` standalone kind signature. For each,
/// parse the sig's outer `forall` + arrow chain to determine
/// which forall-var each arg position binds to, and store the
/// per-position group identifiers under the type's name.
///
/// Used at type-application sites to detect cases like
/// `data Pair :: forall k. k -> k -> Type; type F = Pair Int "foo"`
/// — both positions bind `k`, so the args must have matching
/// primitive kind tags. `Int` is Type, `"foo"` is Symbol →
/// mismatch.
fn build_kind_sig_groups(
    module: &cst::Module,
) -> HashMap<Symbol, Vec<Option<Symbol>>> {
    use std::collections::HashMap as Map;
    let mut out: Map<Symbol, Vec<Option<Symbol>>> = Map::new();
    for d in &module.decls {
        let (name, kind_ty) = match d {
            cst::Decl::Data { name, kind_type: Some(k), .. } => {
                (name.value.symbol(), k.as_ref())
            }
            cst::Decl::Class { name, kind_type: Some(k), .. } => {
                (name.value.symbol(), k.as_ref())
            }
            _ => continue,
        };
        let groups = parse_kind_sig_groups(kind_ty);
        if !groups.is_empty() {
            out.insert(name, groups);
        }
    }
    out
}

/// Per-param-position arrow count for each type with a
/// standalone polykind sig. Used by
/// `check_known_hkt_class_instance` to detect cases where a
/// type's first param is itself a higher-kind (`Type -> Type`)
/// being used in a single-arg HKT class context that wants
/// `Type` there (`derive instance Foldable Foo` for
/// `data Foo :: (Type -> Type) -> Type`).
fn build_kind_sig_param_arrows(
    module: &cst::Module,
) -> HashMap<Symbol, Vec<usize>> {
    use std::collections::HashMap as Map;
    let mut out: Map<Symbol, Vec<usize>> = Map::new();
    for d in &module.decls {
        let (name, kind_ty) = match d {
            cst::Decl::Data { name, kind_type: Some(k), .. } => {
                (name.value.symbol(), k.as_ref())
            }
            cst::Decl::Class { name, kind_type: Some(k), .. } => {
                (name.value.symbol(), k.as_ref())
            }
            _ => continue,
        };
        let arrows = parse_kind_sig_param_arrows(kind_ty);
        if !arrows.is_empty() {
            out.insert(name, arrows);
        }
    }
    out
}

fn parse_kind_sig_param_arrows(te: &cst::TypeExpr) -> Vec<usize> {
    let mut cur = te;
    loop {
        match cur {
            cst::TypeExpr::Forall { ty, .. } => cur = ty,
            cst::TypeExpr::Parens { ty, .. } => cur = ty,
            _ => break,
        }
    }
    let mut arrows: Vec<usize> = Vec::new();
    while let cst::TypeExpr::Function { from, to, .. } = cur {
        arrows.push(arrow_count(from));
        cur = to;
    }
    arrows
}

/// Parse a kind signature `forall k1 k2. K1 -> K2 -> ...` into
/// the per-arg-position forall-var-name (or None for non-Var
/// kinds). Returns one entry per arrow in the kind sig (i.e.
/// per arg position the type accepts).
fn parse_kind_sig_groups(te: &cst::TypeExpr) -> Vec<Option<Symbol>> {
    let mut cur = te;
    let mut foralls: std::collections::HashSet<Symbol> =
        std::collections::HashSet::new();
    loop {
        match cur {
            cst::TypeExpr::Forall { vars, ty, .. } => {
                for (v, _, _) in vars {
                    foralls.insert(v.value.symbol());
                }
                cur = ty;
            }
            cst::TypeExpr::Parens { ty, .. } => cur = ty,
            _ => break,
        }
    }
    let mut groups: Vec<Option<Symbol>> = Vec::new();
    while let cst::TypeExpr::Function { from, to, .. } = cur {
        let arg_var = match from.as_ref() {
            cst::TypeExpr::Var { name, .. } => {
                let s = name.value.symbol();
                if foralls.contains(&s) {
                    Some(s)
                } else {
                    None
                }
            }
            _ => None,
        };
        groups.push(arg_var);
        cur = to;
    }
    groups
}

fn arrow_count(te: &cst::TypeExpr) -> usize {
    match te {
        cst::TypeExpr::Function { to, .. } => 1 + arrow_count(to),
        cst::TypeExpr::Parens { ty, .. } => arrow_count(ty),
        cst::TypeExpr::Forall { ty, .. } => arrow_count(ty),
        _ => 0,
    }
}

/// Strip arrows / forall / parens to find the kind's "output"
/// portion, then classify it as a primitive kind tag.
fn prim_kind_of(te: &cst::TypeExpr) -> Option<PrimKind> {
    let mut cur = te;
    loop {
        match cur {
            cst::TypeExpr::Function { to, .. } => cur = to,
            cst::TypeExpr::Parens { ty, .. } => cur = ty,
            cst::TypeExpr::Forall { ty, .. } => cur = ty,
            cst::TypeExpr::Constructor { name, .. } => {
                let n = resolve(name.name.symbol());
                return match n.as_str() {
                    "Type" => Some(PrimKind::Type),
                    "Symbol" => Some(PrimKind::Symbol),
                    "Int" => Some(PrimKind::Int),
                    "Boolean" => Some(PrimKind::Boolean),
                    "Constraint" => Some(PrimKind::Constraint),
                    _ => Some(PrimKind::Other),
                };
            }
            _ => return None,
        }
    }
}

/// Classify an *argument* expression's primitive kind tag at
/// type-application time. Returns `None` when the arg is a type
/// variable, a hole, a wildcard, or anything we can't classify
/// without full kind inference.
fn arg_prim_kind(te: &cst::TypeExpr) -> Option<PrimKind> {
    match te {
        cst::TypeExpr::StringLiteral { .. } => Some(PrimKind::Symbol),
        cst::TypeExpr::IntLiteral { .. } => Some(PrimKind::Int),
        cst::TypeExpr::Function { .. } => Some(PrimKind::Type),
        cst::TypeExpr::Constructor { name, .. } => {
            let n = resolve(name.name.symbol());
            match n.as_str() {
                "Type" | "Constraint" | "Boolean" | "Symbol" | "Int" => {
                    Some(PrimKind::Type)
                }
                "True" | "False" => Some(PrimKind::Boolean),
                _ => None,
            }
        }
        cst::TypeExpr::Parens { ty, .. } => arg_prim_kind(ty),
        cst::TypeExpr::App { constructor, .. } => arg_prim_kind(constructor),
        cst::TypeExpr::Record { .. } | cst::TypeExpr::Row { .. } => {
            Some(PrimKind::Type)
        }
        _ => None,
    }
}

fn resolve(sym: Symbol) -> String {
    crate::interner::resolve(sym).unwrap_or_default()
}
