//! Instance registry for the M5 constraint solver.
//!
//! Scans a module's `Decl::Instance` entries and collects them into a
//! class-keyed index. The solver consults this index when it needs to
//! discharge a constraint: given `C ts`, the candidates are
//! `index.by_class("C")`.
//!
//! Scope of this file:
//! * Build the index from a decl list.
//! * Store the instance's class, the types it's declared for, its
//!   context (constraints the instance itself depends on), and the
//!   quantified type-variable list so the solver can freshen them
//!   before unification.
//! * Expose the raw `Vec<Instance>` shape under each class. A
//!   canonical-constraint cache layer sits on top of this in Phase D,
//!   not here.
//!
//! Out of scope: solving, fundep analysis, dict-expression recording.
//! Those are implemented in [`crate::typecheck_db::passes::constraints`]
//! and built on top of this index.

use std::collections::HashMap;

use serde::{Deserialize, Serialize};

use crate::typecheck_db::ir::Decl;
use crate::typecheck_db::types::{convert_type_expr, Constraint, QName, Type, TypeOpMap};

// ---------------------------------------------------------------------------
// Data types
// ---------------------------------------------------------------------------

/// One `instance Eq a => Eq (Maybe a) where …` lifted into solver shape.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Instance {
    /// Class the instance implements. Stored as a [`QName`] so the
    /// module qualifier (where the class was declared) travels with
    /// the name; Phase B's solver canonicalizes class references on
    /// both sides before comparing.
    pub class: QName,
    /// The type arguments the instance is declared for, in declaration
    /// order: e.g. `instance Eq (Maybe a)` → `[App(Con(Maybe), Var(a))]`;
    /// `instance MonadState Int MyMonad` → `[Con(Int), Con(MyMonad)]`.
    pub types: Vec<Type>,
    /// Context: `instance Eq a => Eq (Maybe a)` → `[Eq a]`. The solver
    /// propagates these as fresh sub-constraints when the instance
    /// matches.
    pub context: Vec<Constraint>,
    /// Quantified type variables of the instance head, in first-appearance
    /// order. Freshened to unification variables at match time so
    /// different call sites don't alias each other.
    pub vars: Vec<String>,
    /// `chain: true` when this entry sits in an `else`-continued
    /// instance chain. The solver filters chain candidates separately.
    pub chained: bool,
}

/// Per-class metadata the solver uses for fundep-driven matching.
///
/// Populated from each `Decl::Class` the scanner sees. Without
/// fundeps, `fundeps` is empty — the solver falls back to the
/// conservative rule (any unsolved unif argument → defer).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ClassInfo {
    /// The class's declared type parameters, in source order.
    pub type_vars: Vec<String>,
    /// Functional dependencies. Each entry `(determiners, determined)`
    /// is a list of *positions* into `type_vars`.
    pub fundeps: Vec<FunDep>,
    /// Declared superclass constraints — `class Eq a => Ord a`
    /// becomes `superclasses = [Eq a]`. Args are `Type::Var`
    /// references to `type_vars`; consumers substitute when the
    /// class is matched against concrete args. Used by the
    /// solver's given-discharge path to expand givens transitively.
    #[serde(default)]
    pub superclasses: Vec<Constraint>,
}

/// One functional dependency, stored positionally so solver
/// look-ups don't have to re-resolve var names at match time.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FunDep {
    /// Positions (indices into `ClassInfo::type_vars`) whose values
    /// determine the RHS.
    pub determiners: Vec<usize>,
    /// Positions whose values follow from the determiners.
    pub determined: Vec<usize>,
}

/// Class-keyed lookup of instances in scope, plus per-class metadata
/// the solver consults during matching (`ClassInfo` for fundeps).
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct InstanceIndex {
    by_class: HashMap<String, Vec<Instance>>,
    classes: HashMap<String, ClassInfo>,
    /// Coverage-check findings from `from_decls`. An instance whose
    /// head violates its class's fundep coverage lands here rather
    /// than being inserted — Phase D's solver honors the check at
    /// registration time so buggy instances can't corrupt matching.
    #[serde(default)]
    coverage_errors: Vec<CoverageError>,
}

/// Fundep coverage-rule violation: an instance's determined
/// positions mention type variables that its determiner positions
/// don't.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CoverageError {
    pub class: crate::typecheck_db::types::QName,
    pub instance_types: Vec<Type>,
    pub fundep_index: usize,
    /// Type variable names present in determined positions but not
    /// covered by determiners.
    pub uncovered_vars: Vec<String>,
}

impl InstanceIndex {
    pub fn new() -> Self {
        Self::default()
    }

    /// Insert one instance under its declared class key. The index
    /// is keyed by the class's simple name (without module prefix);
    /// canonicalization across module aliases happens at solve time.
    pub fn insert(&mut self, instance: Instance) {
        self.by_class
            .entry(instance.class.name.clone())
            .or_default()
            .push(instance);
    }

    /// All instances declared for `class_name`, in registration order.
    pub fn candidates(&self, class_name: &str) -> &[Instance] {
        self.by_class
            .get(class_name)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    pub fn len(&self) -> usize {
        self.by_class.values().map(Vec::len).sum()
    }

    pub fn is_empty(&self) -> bool {
        self.by_class.is_empty()
    }

    /// Register metadata about a class. Replaces any previous entry
    /// under the same simple name.
    pub fn insert_class(&mut self, class_name: String, info: ClassInfo) {
        self.classes.insert(class_name, info);
    }

    /// Metadata for `class_name`, if the scanner knows about it.
    pub fn class_info(&self, class_name: &str) -> Option<&ClassInfo> {
        self.classes.get(class_name)
    }

    /// Every coverage-rule violation the scanner caught when building
    /// the index. An empty slice means the in-scope instances are
    /// all well-formed with respect to their classes' fundeps.
    pub fn coverage_errors(&self) -> &[CoverageError] {
        &self.coverage_errors
    }

    /// Every `(class_name, instance)` pair the index holds, in
    /// insertion order per class.
    pub fn all_instances(&self) -> impl Iterator<Item = (&str, &Instance)> {
        self.by_class
            .iter()
            .flat_map(|(class, list)| list.iter().map(move |i| (class.as_str(), i)))
    }

    /// Walk every instance head + context and expand type
    /// aliases in-place. Used after the index has been seeded
    /// from imports so that the solver matches on the expanded
    /// form (e.g. a `SynString` → `String` alias in the
    /// importing module canonicalizes instance heads that came
    /// through unexpanded).
    pub fn expand_aliases_in_place(
        &mut self,
        aliases: &crate::typecheck_db::types::AliasMap,
    ) {
        if aliases.is_empty() {
            return;
        }
        for (_, list) in self.by_class.iter_mut() {
            for inst in list.iter_mut() {
                inst.types = inst
                    .types
                    .drain(..)
                    .map(|t| crate::typecheck_db::types::expand_aliases(t, aliases))
                    .collect();
                for c in &mut inst.context {
                    c.args = c
                        .args
                        .drain(..)
                        .map(|t| crate::typecheck_db::types::expand_aliases(t, aliases))
                        .collect();
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Scanner
// ---------------------------------------------------------------------------

/// Pure scanner: walks a decl list and extracts every `Decl::Class`
/// + `Decl::Instance` into an `InstanceIndex`. Classes must be
/// registered before the instances that depend on them so the
/// coverage check has metadata to consult; to avoid caller-ordering
/// constraints, we do two passes.
pub fn from_decls(decls: &[Decl], type_ops: &TypeOpMap) -> InstanceIndex {
    let mut ix = InstanceIndex::new();
    // Pass 1: classes. Fundeps live here; instance coverage in
    // Pass 2 queries them by name.
    for d in decls {
        if let Decl::Class { name, type_vars, fundeps, constraints, .. } = d {
            let class_name =
                crate::typecheck_db::util::resolve_symbol(name.value.symbol());
            let vars: Vec<String> = type_vars
                .iter()
                .map(|v| crate::typecheck_db::util::resolve_symbol(v.value.symbol()))
                .collect();
            let fundeps_pos: Vec<FunDep> = fundeps
                .iter()
                .map(|fd| FunDep {
                    determiners: fd
                        .lhs
                        .iter()
                        .filter_map(|v| position_of(&vars, v))
                        .collect(),
                    determined: fd
                        .rhs
                        .iter()
                        .filter_map(|v| position_of(&vars, v))
                        .collect(),
                })
                .collect();
            let superclasses: Vec<Constraint> = constraints
                .iter()
                .map(|c| Constraint {
                    class: cst_constraint_qname(&c.class),
                    args: c.args.iter().map(|a| convert_type_expr(a, type_ops)).collect(),
                })
                .collect();
            ix.insert_class(
                class_name,
                ClassInfo {
                    type_vars: vars,
                    fundeps: fundeps_pos,
                    superclasses,
                },
            );
        }
    }
    // Pass 2: instances.
    for d in decls {
        if let Decl::Instance {
            constraints,
            class_name,
            types,
            chain,
            ..
        } = d
        {
            let class = resolved_class_qname(class_name);
            let head_tys: Vec<Type> =
                types.iter().map(|t| convert_type_expr(t, type_ops)).collect();
            let context: Vec<Constraint> = constraints
                .iter()
                .map(|c| Constraint {
                    class: cst_constraint_qname(&c.class),
                    args: c
                        .args
                        .iter()
                        .map(|a| convert_type_expr(a, type_ops))
                        .collect(),
                })
                .collect();
            let vars = collect_instance_vars(&head_tys, &context);
            // Coverage check: for every fundep, determined-position
            // vars must be a subset of determiner-position vars.
            let class_info_opt = ix.class_info(&class.name).cloned();
            if let Some(info) = class_info_opt {
                for (idx, fd) in info.fundeps.iter().enumerate() {
                    let lhs_vars = collect_vars_at_positions(&head_tys, &fd.determiners);
                    let rhs_vars = collect_vars_at_positions(&head_tys, &fd.determined);
                    let uncovered: Vec<String> = rhs_vars
                        .into_iter()
                        .filter(|v| !lhs_vars.contains(v))
                        .collect();
                    if !uncovered.is_empty() {
                        ix.coverage_errors.push(CoverageError {
                            class: class.clone(),
                            instance_types: head_tys.clone(),
                            fundep_index: idx,
                            uncovered_vars: uncovered,
                        });
                    }
                }
            }
            ix.insert(Instance {
                class,
                types: head_tys,
                context,
                vars,
                chained: *chain,
            });
        }
    }
    ix
}

fn cst_constraint_qname(
    q: &crate::names::Qualified<crate::names::ClassName>,
) -> crate::typecheck_db::types::QName {
    crate::typecheck_db::types::QName {
        module: q
            .module
            .map(|m| crate::typecheck_db::util::resolve_symbol(m.symbol())),
        name: crate::typecheck_db::util::resolve_symbol(q.name.symbol()),
    }
}

/// Variant of `cst_constraint_qname` for `Resolved<ClassName>`
/// (used by IR instance/derive class-name positions). Classes are
/// always module-level; in production every class ref should
/// resolve. We tolerate the unresolved sentinel here because
/// scanner unit tests build IR without running `resolve_pass` and
/// rely on this graceful fall-through.
fn resolved_class_qname(
    q: &crate::names::Resolved<crate::names::ClassName>,
) -> crate::typecheck_db::types::QName {
    crate::typecheck_db::types::QName {
        module: if q.module.is_unresolved() {
            None
        } else {
            Some(crate::typecheck_db::util::resolve_symbol(q.module.symbol()))
        },
        name: crate::typecheck_db::util::resolve_symbol(q.name.symbol()),
    }
}

fn position_of(vars: &[String], tv: &crate::names::TypeVarName) -> Option<usize> {
    let name = crate::typecheck_db::util::resolve_symbol(tv.symbol());
    vars.iter().position(|v| v == &name)
}

/// Collect the free type variables that appear in the type
/// arguments at the given positions. Used by the coverage check
/// to compare determiner-position vars with determined-position
/// vars.
fn collect_vars_at_positions(types: &[Type], positions: &[usize]) -> Vec<String> {
    let mut out = Vec::new();
    for &p in positions {
        if let Some(ty) = types.get(p) {
            collect_vars_into(ty, &mut out);
        }
    }
    out
}

/// Best-effort collector for free type variables in an instance's
/// head — used by the scanner to populate `Instance::vars`.
///
/// The PureScript parser doesn't explicitly quantify instance vars;
/// they're whatever `Var` names appear in the head or context. We
/// collect in first-appearance order so freshening at match time
/// produces deterministic unification vars.
pub fn collect_instance_vars(types: &[Type], context: &[Constraint]) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    for t in types {
        collect_vars_into(t, &mut out);
    }
    for c in context {
        for a in &c.args {
            collect_vars_into(a, &mut out);
        }
    }
    out
}

fn collect_vars_into(ty: &Type, out: &mut Vec<String>) {
    match ty {
        Type::Var(name) => {
            if !out.contains(name) {
                out.push(name.clone());
            }
        }
        Type::App(f, a) => {
            collect_vars_into(f, out);
            collect_vars_into(a, out);
        }
        Type::Fun(f, t) => {
            collect_vars_into(f, out);
            collect_vars_into(t, out);
        }
        Type::Forall(vars, body) => {
            // A nested forall shadows names locally — strip them before
            // continuing. (Rare inside instance heads, but correct.)
            let saved_len = out.len();
            let quantified: std::collections::HashSet<&str> =
                vars.iter().map(|(n, _, _)| n.as_str()).collect();
            let mut inner: Vec<String> = Vec::new();
            collect_vars_into(body, &mut inner);
            for name in inner {
                if !quantified.contains(name.as_str()) && !out.contains(&name) {
                    out.push(name);
                }
            }
            let _ = saved_len;
        }
        Type::Constrained(cs, body) => {
            for c in cs {
                for a in &c.args {
                    collect_vars_into(a, out);
                }
            }
            collect_vars_into(body, out);
        }
        Type::Record(fs, tail) | Type::Row(fs, tail) => {
            for (_, t) in fs {
                collect_vars_into(t, out);
            }
            if let Some(t) = tail {
                collect_vars_into(t, out);
            }
        }
        Type::Kinded(t, k) => {
            collect_vars_into(t, out);
            collect_vars_into(k, out);
        }
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse;
    use crate::typecheck_db::types::QName;

    fn type_con(name: &str) -> Type {
        Type::Con(QName::unqualified(name))
    }

    fn parse_module(src: &str) -> Vec<Decl> {
        use crate::typecheck_db::desugar::{
            desugar_module, fixity_table_from_decls, DesugarContext,
        };
        let cst_mod = parse(src).unwrap();
        let (fixity_table, module_fixity_hash) = fixity_table_from_decls(&cst_mod.decls);
        let ctx = DesugarContext { module_fixity_hash, fixity_table };
        let decls = desugar_module(cst_mod.decls.clone(), &ctx);
        let desugared = crate::cst::Module { decls, ..cst_mod };
        crate::typecheck_db::ir::lower_module(desugared)
            .expect("cst → ir lowering")
            .decls
    }

    // =================================================================
    // Manual construction + basic operations
    // =================================================================

    #[test]
    fn new_index_is_empty() {
        let ix = InstanceIndex::new();
        assert!(ix.is_empty());
        assert_eq!(ix.len(), 0);
    }

    #[test]
    fn insert_one_bumps_count() {
        let mut ix = InstanceIndex::new();
        ix.insert(Instance {
            class: QName::unqualified("Eq"),
            types: vec![type_con("Int")],
            context: vec![],
            vars: vec![],
            chained: false,
        });
        assert_eq!(ix.len(), 1);
        assert_eq!(ix.candidates("Eq").len(), 1);
        assert_eq!(ix.candidates("Show").len(), 0);
    }

    #[test]
    fn candidates_preserves_insertion_order() {
        let mut ix = InstanceIndex::new();
        let base = Instance {
            class: QName::unqualified("Show"),
            types: vec![],
            context: vec![],
            vars: vec![],
            chained: false,
        };
        ix.insert(Instance { types: vec![type_con("Int")], ..base.clone() });
        ix.insert(Instance { types: vec![type_con("String")], ..base.clone() });
        ix.insert(Instance { types: vec![type_con("Char")], ..base });

        let cands = ix.candidates("Show");
        assert_eq!(cands.len(), 3);
        assert_eq!(cands[0].types[0], type_con("Int"));
        assert_eq!(cands[1].types[0], type_con("String"));
        assert_eq!(cands[2].types[0], type_con("Char"));
    }

    // =================================================================
    // collect_instance_vars
    // =================================================================

    #[test]
    fn collect_vars_empty_for_monotype_head() {
        // `Eq Int` — no vars.
        let vars = collect_instance_vars(&[type_con("Int")], &[]);
        assert!(vars.is_empty());
    }

    #[test]
    fn collect_vars_from_head_only() {
        // `Eq (Maybe a)` → [a].
        let ty = Type::app(type_con("Maybe"), Type::Var("a".into()));
        let vars = collect_instance_vars(&[ty], &[]);
        assert_eq!(vars, vec!["a".to_string()]);
    }

    #[test]
    fn collect_vars_preserves_first_appearance_order() {
        // `Bifunctor f a b` (hypothetical) → [f, a, b] in appearance
        // order, even if `a` and `b` repeat.
        let types = vec![
            Type::Var("f".into()),
            Type::Var("a".into()),
            Type::Var("b".into()),
            Type::Var("a".into()),
        ];
        let vars = collect_instance_vars(&types, &[]);
        assert_eq!(vars, vec!["f".to_string(), "a".into(), "b".into()]);
    }

    #[test]
    fn collect_vars_merges_context_vars() {
        // `instance Eq a => Show (Maybe a)` — both head and context
        // mention `a`; should dedupe.
        let head = Type::app(type_con("Maybe"), Type::Var("a".into()));
        let ctx = vec![Constraint {
            class: QName::unqualified("Eq"),
            args: vec![Type::Var("a".into())],
        }];
        let vars = collect_instance_vars(&[head], &ctx);
        assert_eq!(vars, vec!["a".to_string()]);
    }

    // =================================================================
    // from_decls — scanner behavior
    // =================================================================

    #[test]
    fn scanner_ignores_non_instance_decls() {
        let decls = parse_module(
            "\
module M where
x = 1
data T = A | B
",
        );
        let ix = from_decls(&decls, &TypeOpMap::default());
        assert!(ix.is_empty());
    }

    #[test]
    fn scanner_registers_simple_instance() {
        let decls = parse_module(
            "\
module M where
instance Eq Int where
  eq x y = true
",
        );
        let ix = from_decls(&decls, &TypeOpMap::default());
        let cands = ix.candidates("Eq");
        assert_eq!(cands.len(), 1);
        assert_eq!(cands[0].class.name, "Eq");
        assert_eq!(cands[0].types, vec![type_con("Int")]);
        assert!(cands[0].context.is_empty());
        assert!(cands[0].vars.is_empty());
    }

    #[test]
    fn scanner_handles_parenthesized_polymorphic_head() {
        // `instance Eq a => Eq (Maybe a)` — head is `Maybe a`, context
        // is `[Eq a]`, vars are `[a]`.
        let decls = parse_module(
            "\
module M where
instance Eq a => Eq (Maybe a) where
  eq x y = true
",
        );
        let ix = from_decls(&decls, &TypeOpMap::default());
        let cands = ix.candidates("Eq");
        assert_eq!(cands.len(), 1);
        let inst = &cands[0];
        assert_eq!(inst.class.name, "Eq");
        assert_eq!(inst.vars, vec!["a".to_string()]);
        assert_eq!(inst.context.len(), 1);
        assert_eq!(inst.context[0].class.name, "Eq");
        assert_eq!(inst.context[0].args, vec![Type::Var("a".into())]);
        assert_eq!(
            inst.types,
            vec![Type::app(type_con("Maybe"), Type::Var("a".into()))],
        );
    }

    #[test]
    fn scanner_ignores_user_given_instance_name() {
        // User-provided names like `eqInt ::` are parser-preserved
        // but don't affect the index. Codegen generates stable names
        // from the instance's shape itself.
        let decls = parse_module(
            "\
module M where
instance eqInt :: Eq Int where
  eq x y = true
",
        );
        let ix = from_decls(&decls, &TypeOpMap::default());
        let cands = ix.candidates("Eq");
        assert_eq!(cands.len(), 1);
        assert_eq!(cands[0].class.name, "Eq");
        assert_eq!(cands[0].types, vec![type_con("Int")]);
    }

    #[test]
    fn scanner_groups_multiple_instances_under_same_class() {
        let decls = parse_module(
            "\
module M where
instance Show Int where
  show _ = \"Int\"
instance Show String where
  show _ = \"String\"
",
        );
        let ix = from_decls(&decls, &TypeOpMap::default());
        let cands = ix.candidates("Show");
        assert_eq!(cands.len(), 2);
        assert_eq!(cands[0].types, vec![type_con("Int")]);
        assert_eq!(cands[1].types, vec![type_con("String")]);
    }

    #[test]
    fn scanner_handles_multi_param_instance_head() {
        // `class MonadState s m | m -> s` — instance has two types.
        let decls = parse_module(
            "\
module M where
instance MonadState Int MyMonad where
  get = get'
  put _ = put'
",
        );
        let ix = from_decls(&decls, &TypeOpMap::default());
        let cands = ix.candidates("MonadState");
        assert_eq!(cands.len(), 1);
        assert_eq!(cands[0].types.len(), 2);
        assert_eq!(cands[0].types[0], type_con("Int"));
        assert_eq!(cands[0].types[1], type_con("MyMonad"));
    }

    #[test]
    fn scanner_marks_chained_instances() {
        // `else instance ...` continues a chain. The scanner should
        // set `chained: true` on the continuation.
        let decls = parse_module(
            "\
module M where
instance IsInt Int where
  isInt = true
else instance IsInt a where
  isInt = false
",
        );
        let ix = from_decls(&decls, &TypeOpMap::default());
        let cands = ix.candidates("IsInt");
        assert_eq!(cands.len(), 2);
        assert!(!cands[0].chained);
        assert!(cands[1].chained);
    }

    #[test]
    fn scanner_walks_multiple_context_constraints() {
        let decls = parse_module(
            "\
module M where
instance (Eq a, Show a) => Pretty (Maybe a) where
  pretty _ = \"…\"
",
        );
        let ix = from_decls(&decls, &TypeOpMap::default());
        let cands = ix.candidates("Pretty");
        assert_eq!(cands.len(), 1);
        assert_eq!(cands[0].context.len(), 2);
        let names: Vec<&str> = cands[0]
            .context
            .iter()
            .map(|c| c.class.name.as_str())
            .collect();
        assert!(names.contains(&"Eq"));
        assert!(names.contains(&"Show"));
    }

    // =================================================================
    // Phase D: class metadata + fundeps
    // =================================================================

    #[test]
    fn scanner_registers_class_with_no_fundeps() {
        let decls = parse_module(
            "\
module M where
class Eq a where
  eq :: a -> a -> Boolean
",
        );
        let ix = from_decls(&decls, &TypeOpMap::default());
        let info = ix.class_info("Eq").expect("class Eq registered");
        assert_eq!(info.type_vars, vec!["a".to_string()]);
        assert!(info.fundeps.is_empty());
    }

    #[test]
    fn scanner_registers_single_fundep() {
        // `class MonadState s m | m -> s`: determiners = [m] = [1],
        // determined = [s] = [0].
        let decls = parse_module(
            "\
module M where
class MonadState s m | m -> s where
  get :: m
",
        );
        let ix = from_decls(&decls, &TypeOpMap::default());
        let info = ix.class_info("MonadState").unwrap();
        assert_eq!(info.type_vars, vec!["s".to_string(), "m".to_string()]);
        assert_eq!(info.fundeps.len(), 1);
        assert_eq!(info.fundeps[0].determiners, vec![1]);
        assert_eq!(info.fundeps[0].determined, vec![0]);
    }

    #[test]
    fn scanner_registers_multi_fundep_bidirectional() {
        // Row.Cons-style multi-fundep.
        let decls = parse_module(
            "\
module M where
class Cons h t from to | h t -> from, h t -> to, from h -> t where
  push :: h
",
        );
        let ix = from_decls(&decls, &TypeOpMap::default());
        let info = ix.class_info("Cons").unwrap();
        assert_eq!(info.type_vars, vec!["h".to_string(), "t".into(), "from".into(), "to".into()]);
        assert_eq!(info.fundeps.len(), 3);
        // First fundep: h t -> from
        assert_eq!(info.fundeps[0].determiners, vec![0, 1]);
        assert_eq!(info.fundeps[0].determined, vec![2]);
        // Second: h t -> to
        assert_eq!(info.fundeps[1].determiners, vec![0, 1]);
        assert_eq!(info.fundeps[1].determined, vec![3]);
        // Third: from h -> t
        assert_eq!(info.fundeps[2].determiners, vec![2, 0]);
        assert_eq!(info.fundeps[2].determined, vec![1]);
    }

    #[test]
    fn scanner_accepts_instance_with_good_coverage() {
        // `class C a b | a -> b`; `instance C Int Bool` — both
        // positions concrete, no uncovered var.
        let decls = parse_module(
            "\
module M where
class C a b | a -> b where
  m :: a -> b
instance C Int Boolean where
  m _ = true
",
        );
        let ix = from_decls(&decls, &TypeOpMap::default());
        assert!(
            ix.coverage_errors().is_empty(),
            "got: {:?}",
            ix.coverage_errors(),
        );
    }

    #[test]
    fn scanner_flags_coverage_violation_when_rhs_var_is_free() {
        // `class C a b | a -> b`; `instance C Int c` — c is declared
        // on the RHS of the fundep but not present in the LHS
        // position. Coverage rule violated.
        let decls = parse_module(
            "\
module M where
class C a b | a -> b where
  m :: a -> b
instance C Int c where
  m _ = m'
",
        );
        let ix = from_decls(&decls, &TypeOpMap::default());
        let errs = ix.coverage_errors();
        assert_eq!(errs.len(), 1, "got: {errs:?}");
        assert_eq!(errs[0].class.name, "C");
        assert_eq!(errs[0].fundep_index, 0);
        assert_eq!(errs[0].uncovered_vars, vec!["c".to_string()]);
    }

    #[test]
    fn scanner_does_not_flag_when_rhs_fully_covered_via_ctor_args() {
        // `class C a b | a -> b`; `instance C (Maybe a) (List a)` —
        // the var `a` appears on both sides, so coverage holds.
        let decls = parse_module(
            "\
module M where
class C a b | a -> b where
  m :: a -> b
instance C (Maybe a) (List a) where
  m _ = nil
",
        );
        let ix = from_decls(&decls, &TypeOpMap::default());
        assert!(ix.coverage_errors().is_empty(), "got: {:?}", ix.coverage_errors());
    }

    #[test]
    fn class_info_missing_for_unknown_class_is_none() {
        let ix = InstanceIndex::new();
        assert!(ix.class_info("DoesNotExist").is_none());
    }
}
