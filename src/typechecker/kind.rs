use std::collections::{HashMap, HashSet};

use crate::ast::span::Span;
use crate::cst::TypeExpr;
use crate::interner::{self, Symbol};
use crate::typechecker::error::TypeError;
use crate::typechecker::types::Type;
use crate::typechecker::unify::UnifyState;

/// Kind-checking state: a separate UnifyState for kind unification,
/// plus a mapping from type constructor names to their kinds.
pub struct KindState {
    pub state: UnifyState,
    /// Maps type constructor names (e.g. "Array", "Maybe") to their kinds.
    pub type_kinds: HashMap<Symbol, Type>,
    /// Types in the current binding group (SCC). Lookups for these types
    /// skip freshening to enable monomorphic kind inference within the group.
    pub binding_group: HashSet<Symbol>,
}

impl KindState {
    /// Create a new KindState pre-populated with built-in (Prim) kinds.
    pub fn new() -> Self {
        let mut type_kinds = HashMap::new();
        let k_type = Type::kind_type();

        // Prim types with kind Type
        for name in &[
            "Int", "Number", "String", "Char", "Boolean", "Unit",
        ] {
            type_kinds.insert(interner::intern(name), k_type.clone());
        }

        // Array :: Type -> Type
        type_kinds.insert(
            interner::intern("Array"),
            Type::fun(k_type.clone(), k_type.clone()),
        );

        // Record :: Row Type -> Type
        type_kinds.insert(
            interner::intern("Record"),
            Type::fun(Type::kind_row_of(k_type.clone()), k_type.clone()),
        );

        // Function ((->) :: Type -> Type -> Type
        type_kinds.insert(
            interner::intern("->"),
            Type::fun(k_type.clone(), Type::fun(k_type.clone(), k_type.clone())),
        );
        type_kinds.insert(
            interner::intern("Function"),
            Type::fun(k_type.clone(), Type::fun(k_type.clone(), k_type.clone())),
        );

        // Prim.Row.Union :: forall k. Row k -> Row k -> Row k -> Constraint
        // (we don't need this for basic kind checking)

        // Type :: Type (kind of kinds — self-referential, but fine for our purposes)
        type_kinds.insert(interner::intern("Type"), k_type.clone());
        type_kinds.insert(interner::intern("Constraint"), k_type.clone());
        type_kinds.insert(interner::intern("Symbol"), k_type.clone());
        // Row :: Type -> Type (Row is a kind constructor)
        type_kinds.insert(
            interner::intern("Row"),
            Type::fun(k_type.clone(), k_type.clone()),
        );

        // Well-known classes: (Type -> Type) -> Constraint
        // These are safe to register as builtins because they're standard and their
        // kind is well-established. Modules that define them locally will override
        // in Pass A. Modules that import them will use these kinds for instance head checking.
        let k_constraint = Type::kind_constraint();
        let k_type_to_type = Type::fun(k_type.clone(), k_type.clone());
        let k_type1_to_constraint = Type::fun(k_type_to_type.clone(), k_constraint.clone());
        for name in &[
            "Functor", "Foldable", "Traversable",
            "Apply", "Applicative", "Bind", "Monad",
            "Alt", "Plus", "Alternative",
            "Extend", "Comonad",
            "Unfoldable", "Unfoldable1",
        ] {
            type_kinds.insert(interner::intern(name), k_type1_to_constraint.clone());
        }

        // Well-known classes: Type -> Constraint
        let k_type_to_constraint = Type::fun(k_type.clone(), k_constraint.clone());
        for name in &[
            "Eq", "Ord", "Show", "Bounded", "HeytingAlgebra", "BooleanAlgebra",
            "Semiring", "Ring", "CommutativeRing", "EuclideanRing", "Field",
            "Semigroup", "Monoid",
        ] {
            type_kinds.insert(interner::intern(name), k_type_to_constraint.clone());
        }

        KindState {
            state: UnifyState::new(),
            type_kinds,
            binding_group: HashSet::new(),
        }
    }

    /// Create a fresh kind unification variable.
    pub fn fresh_kind_var(&mut self) -> Type {
        Type::Unif(self.state.fresh_var())
    }

    /// Unify two kinds, mapping unification errors to kind-specific errors.
    pub fn unify_kinds(&mut self, span: Span, expected: &Type, found: &Type) -> Result<(), TypeError> {
        self.state.unify(span, expected, found).map_err(|e| match e {
            TypeError::UnificationError { span, expected, found } => {
                TypeError::KindMismatch { span, expected, found }
            }
            TypeError::InfiniteType { span, var, ty } => {
                TypeError::InfiniteKind { span, var, ty }
            }
            other => other,
        })
    }

    /// Zonk a kind (resolve solved unification variables).
    pub fn zonk_kind(&mut self, k: Type) -> Type {
        self.state.zonk(k)
    }

    /// Register a type constructor with its kind.
    pub fn register_type(&mut self, name: Symbol, kind: Type) {
        self.type_kinds.insert(name, kind);
    }

    /// Look up the kind of a type constructor, freshening unsolved unification
    /// variables so that each usage gets its own copy (prevents cross-contamination
    /// between declarations that share kind variables).
    pub fn lookup_type_fresh(&mut self, name: Symbol) -> Option<Type> {
        let kind = self.type_kinds.get(&name)?.clone();
        let zonked = self.zonk_kind(kind);
        Some(self.freshen_unif_vars(&zonked))
    }

    /// Replace unsolved unification variables in a kind with fresh ones.
    /// This is like instantiation for polymorphic kinds but for unif vars.
    fn freshen_unif_vars(&mut self, ty: &Type) -> Type {
        let mut mapping = HashMap::new();
        self.freshen_unif_vars_inner(ty, &mut mapping)
    }

    fn freshen_unif_vars_inner(&mut self, ty: &Type, mapping: &mut HashMap<crate::typechecker::types::TyVarId, Type>) -> Type {
        match ty {
            Type::Unif(id) => {
                if let Some(solved) = self.state.probe(*id) {
                    self.freshen_unif_vars_inner(&solved, mapping)
                } else {
                    mapping.entry(*id).or_insert_with(|| self.fresh_kind_var()).clone()
                }
            }
            Type::Fun(from, to) => {
                Type::fun(
                    self.freshen_unif_vars_inner(from, mapping),
                    self.freshen_unif_vars_inner(to, mapping),
                )
            }
            Type::App(f, a) => {
                Type::app(
                    self.freshen_unif_vars_inner(f, mapping),
                    self.freshen_unif_vars_inner(a, mapping),
                )
            }
            Type::Forall(vars, body) => {
                Type::Forall(vars.clone(), Box::new(self.freshen_unif_vars_inner(body, mapping)))
            }
            _ => ty.clone(),
        }
    }

    /// Look up the kind of a type constructor (immutable reference).
    pub fn lookup_type(&self, name: Symbol) -> Option<&Type> {
        self.type_kinds.get(&name)
    }
}

/// Check if a kind expression contains unsupported constructs (like constraints).
/// Returns an error if a constraint is used in a kind position.
pub fn check_kind_expr_supported(kind_expr: &TypeExpr) -> Result<(), TypeError> {
    match kind_expr {
        TypeExpr::Constrained { span, .. } => {
            Err(TypeError::UnsupportedTypeInKind { span: *span })
        }
        TypeExpr::Function { from, to, .. } => {
            check_kind_expr_supported(from)?;
            check_kind_expr_supported(to)
        }
        TypeExpr::App { constructor, arg, .. } => {
            check_kind_expr_supported(constructor)?;
            check_kind_expr_supported(arg)
        }
        TypeExpr::Forall { ty, .. } => check_kind_expr_supported(ty),
        TypeExpr::Parens { ty, .. } => check_kind_expr_supported(ty),
        _ => Ok(()),
    }
}

/// Check a type expression for partially applied type synonyms.
/// This catches cases like `(~>) Array` where `~>` is an alias for `NaturalTransformation`
/// (arity 2) but only applied to 1 argument.
pub fn check_type_expr_partial_synonym(
    te: &TypeExpr,
    type_aliases: &HashMap<Symbol, (Vec<Symbol>, crate::typechecker::types::Type)>,
    type_ops: &HashMap<Symbol, Symbol>,
) -> Result<(), TypeError> {
    // Count applied arguments and find the constructor at the head
    fn count_args(te: &TypeExpr) -> (&TypeExpr, usize) {
        match te {
            TypeExpr::App { constructor, .. } => {
                let (head, n) = count_args(constructor);
                (head, n + 1)
            }
            other => (other, 0),
        }
    }

    match te {
        TypeExpr::App { .. } => {
            let (head, arg_count) = count_args(te);
            // Check if head is a type synonym (directly or via type operator resolution)
            let alias_name = match head {
                TypeExpr::Constructor { name, .. } => {
                    if type_aliases.contains_key(&name.name) {
                        Some(name.name)
                    } else {
                        // Operator-as-constructor like (~>) resolves to a type alias
                        type_ops.get(&name.name).copied()
                    }
                }
                TypeExpr::Var { name, .. } => {
                    type_ops.get(&name.value).copied()
                }
                _ => None,
            };
            if let Some(name) = alias_name {
                if let Some((params, _)) = type_aliases.get(&name) {
                    if arg_count < params.len() {
                        return Err(TypeError::PartiallyAppliedSynonym {
                            span: te.span(),
                            name,
                        });
                    }
                }
            }
            // Recurse into argument sub-expressions only (not the constructor spine,
            // which we already checked above via count_args). Also recurse into the
            // head if it's a complex expression (not a simple constructor/var).
            fn collect_app_args<'a>(te: &'a TypeExpr, args: &mut Vec<&'a TypeExpr>) {
                if let TypeExpr::App { constructor, arg, .. } = te {
                    collect_app_args(constructor, args);
                    args.push(arg);
                }
            }
            let mut args = Vec::new();
            collect_app_args(te, &mut args);
            for arg in args {
                check_type_expr_partial_synonym(arg, type_aliases, type_ops)?;
            }
            // Check head if it's not a simple Constructor/Var (those were checked above)
            match head {
                TypeExpr::Constructor { .. } | TypeExpr::Var { .. } => {}
                other => check_type_expr_partial_synonym(other, type_aliases, type_ops)?,
            }
            Ok(())
        }
        TypeExpr::Constructor { name, .. } => {
            // Unapplied constructor — check if it's a synonym with params
            // Also resolve through type_ops for operator-as-constructor like (~>)
            let resolved = if type_aliases.contains_key(&name.name) {
                Some(name.name)
            } else {
                type_ops.get(&name.name).copied()
            };
            if let Some(alias_name) = resolved {
                if let Some((params, _)) = type_aliases.get(&alias_name) {
                    if !params.is_empty() {
                        return Err(TypeError::PartiallyAppliedSynonym {
                            span: te.span(),
                            name: alias_name,
                        });
                    }
                }
            }
            Ok(())
        }
        TypeExpr::TypeOp { span, op, left, right, .. } => {
            // Resolve the operator to its target type name
            let op_name = op.value.name;
            let resolved = type_ops.get(&op_name).copied().unwrap_or(op_name);
            if let Some((params, _)) = type_aliases.get(&resolved) {
                // TypeOp always has 2 args (left and right)
                if 2 < params.len() {
                    return Err(TypeError::PartiallyAppliedSynonym {
                        span: *span,
                        name: resolved,
                    });
                }
            }
            check_type_expr_partial_synonym(left, type_aliases, type_ops)?;
            check_type_expr_partial_synonym(right, type_aliases, type_ops)
        }
        TypeExpr::Function { from, to, .. } => {
            check_type_expr_partial_synonym(from, type_aliases, type_ops)?;
            check_type_expr_partial_synonym(to, type_aliases, type_ops)
        }
        TypeExpr::Forall { ty, vars, .. } => {
            // Check kind annotations on forall vars
            for (_, _, kind_ann) in vars {
                if let Some(k) = kind_ann {
                    check_type_expr_partial_synonym(k, type_aliases, type_ops)?;
                }
            }
            check_type_expr_partial_synonym(ty, type_aliases, type_ops)
        }
        TypeExpr::Parens { ty, .. } => {
            check_type_expr_partial_synonym(ty, type_aliases, type_ops)
        }
        TypeExpr::Constrained { ty, .. } => {
            check_type_expr_partial_synonym(ty, type_aliases, type_ops)
        }
        TypeExpr::Kinded { ty, kind, .. } => {
            check_type_expr_partial_synonym(ty, type_aliases, type_ops)?;
            check_type_expr_partial_synonym(kind, type_aliases, type_ops)
        }
        _ => Ok(()),
    }
}

/// Walk a type expression and check only the KIND ANNOTATIONS (inside `Kinded` and forall
/// var kind annotations) for partially applied type synonyms. Does NOT check the types
/// themselves — those are valid to use as higher-kinded arguments.
pub fn check_kind_annotations_for_partial_synonym(
    te: &TypeExpr,
    type_aliases: &HashMap<Symbol, (Vec<Symbol>, crate::typechecker::types::Type)>,
    type_ops: &HashMap<Symbol, Symbol>,
) -> Result<(), TypeError> {
    match te {
        TypeExpr::Kinded { kind, ty, .. } => {
            // Check the kind annotation for partial synonyms
            check_type_expr_partial_synonym(kind, type_aliases, type_ops)?;
            // Recurse into the type part
            check_kind_annotations_for_partial_synonym(ty, type_aliases, type_ops)
        }
        TypeExpr::Forall { vars, ty, .. } => {
            // Check kind annotations on forall-bound vars
            for (_, _, kind_ann) in vars {
                if let Some(k) = kind_ann {
                    check_type_expr_partial_synonym(k, type_aliases, type_ops)?;
                }
            }
            check_kind_annotations_for_partial_synonym(ty, type_aliases, type_ops)
        }
        TypeExpr::App { constructor, arg, .. } => {
            check_kind_annotations_for_partial_synonym(constructor, type_aliases, type_ops)?;
            check_kind_annotations_for_partial_synonym(arg, type_aliases, type_ops)
        }
        TypeExpr::Function { from, to, .. } => {
            check_kind_annotations_for_partial_synonym(from, type_aliases, type_ops)?;
            check_kind_annotations_for_partial_synonym(to, type_aliases, type_ops)
        }
        TypeExpr::Constrained { ty, .. } => {
            check_kind_annotations_for_partial_synonym(ty, type_aliases, type_ops)
        }
        TypeExpr::Parens { ty, .. } => {
            check_kind_annotations_for_partial_synonym(ty, type_aliases, type_ops)
        }
        TypeExpr::Record { fields, .. } | TypeExpr::Row { fields, .. } => {
            for f in fields {
                check_kind_annotations_for_partial_synonym(&f.ty, type_aliases, type_ops)?;
            }
            Ok(())
        }
        _ => Ok(()),
    }
}

/// Convert a CST TypeExpr used as a kind annotation into a Type representing a kind.
/// E.g., `Type -> Type` becomes `Fun(Con("Type"), Con("Type"))`.
pub fn convert_kind_expr(kind_expr: &TypeExpr) -> Type {
    match kind_expr {
        TypeExpr::Constructor { name, .. } => {
            Type::Con(name.name)
        }
        TypeExpr::Var { name, .. } => {
            Type::Var(name.value)
        }
        TypeExpr::Function { from, to, .. } => {
            Type::fun(convert_kind_expr(from), convert_kind_expr(to))
        }
        TypeExpr::App { constructor, arg, .. } => {
            Type::app(convert_kind_expr(constructor), convert_kind_expr(arg))
        }
        TypeExpr::Forall { vars, ty, .. } => {
            let var_symbols: Vec<_> = vars.iter().map(|(v, vis, _kind)| (v.value, *vis)).collect();
            Type::Forall(var_symbols, Box::new(convert_kind_expr(ty)))
        }
        TypeExpr::Parens { ty, .. } => convert_kind_expr(ty),
        TypeExpr::Kinded { ty, .. } => convert_kind_expr(ty),
        // Fallback for anything else (shouldn't appear in kind annotations)
        _ => Type::kind_type(),
    }
}

/// Infer the kind of a CST TypeExpr.
///
/// `ks` — the KindState with type constructor kinds and unification state
/// `type_var_kinds` — mapping from type variable names to their kinds
/// `type_ops` — mapping from type-level operator symbols to their target type constructor names
/// `self_type` — if Some, the name of the type currently being defined (used to avoid
///   freshening kind vars for self-referencing types, enabling infinite kind detection).
///   Also controls binding-group freshening via `binding_group` field of KindState.
pub fn infer_kind(
    ks: &mut KindState,
    te: &TypeExpr,
    type_var_kinds: &HashMap<Symbol, Type>,
    type_ops: &HashMap<Symbol, Symbol>,
    self_type: Option<Symbol>,
) -> Result<Type, TypeError> {
    match te {
        TypeExpr::Constructor { name, .. } => {
            // Check if this is a type operator used as a constructor
            if let Some(&target) = type_ops.get(&name.name) {
                // Don't freshen for self-referencing or binding group members
                let lookup = if self_type == Some(target) || ks.binding_group.contains(&target) {
                    ks.lookup_type(target).cloned()
                } else {
                    ks.lookup_type_fresh(target)
                };
                if let Some(kind) = lookup {
                    return Ok(kind);
                }
            }
            // Don't freshen for self-referencing types or binding group members
            let in_group = self_type == Some(name.name) || ks.binding_group.contains(&name.name);
            let lookup = if in_group {
                ks.lookup_type(name.name).cloned()
            } else {
                ks.lookup_type_fresh(name.name)
            };
            match lookup {
                Some(kind) => Ok(kind),
                None => {
                    // Check for qualified name
                    if let Some(m) = name.module {
                        let mod_str = interner::resolve(m).unwrap_or_default();
                        let name_str = interner::resolve(name.name).unwrap_or_default();
                        let qualified = interner::intern(&format!("{}.{}", mod_str, name_str));
                        if let Some(kind) = ks.lookup_type_fresh(qualified) {
                            return Ok(kind);
                        }
                    }
                    // Unknown type constructor — use a fresh kind variable so its kind
                    // is inferred from usage. UnknownType errors are handled separately
                    // during the type conversion pass.
                    Ok(ks.fresh_kind_var())
                }
            }
        }

        TypeExpr::Var { name, .. } => {
            match type_var_kinds.get(&name.value) {
                Some(kind) => Ok(kind.clone()),
                None => {
                    // Unknown type variable — produce a fresh kind var
                    // This handles implicit kind polymorphism
                    Ok(ks.fresh_kind_var())
                }
            }
        }

        TypeExpr::App { span, constructor, arg } => {
            let f_kind = infer_kind(ks, constructor, type_var_kinds, type_ops, self_type)?;
            // Instantiate polymorphic (Forall) kinds before application
            let f_kind = instantiate_kind(ks, &f_kind);
            let a_kind = infer_kind(ks, arg, type_var_kinds, type_ops, self_type)?;

            // f_kind should be k1 -> k2; unify k1 with a_kind, return k2
            let result_kind = ks.fresh_kind_var();
            let expected_f_kind = Type::fun(a_kind, result_kind.clone());
            ks.unify_kinds(*span, &expected_f_kind, &f_kind)?;
            Ok(result_kind)
        }

        TypeExpr::Function { span, from, to } => {
            let k_type = Type::kind_type();
            let from_kind = infer_kind(ks, from, type_var_kinds, type_ops, self_type)?;
            ks.unify_kinds(*span, &k_type, &from_kind)?;
            let to_kind = infer_kind(ks, to, type_var_kinds, type_ops, self_type)?;
            ks.unify_kinds(*span, &k_type, &to_kind)?;
            Ok(k_type)
        }

        TypeExpr::Forall { vars, ty, .. } => {
            let mut inner_var_kinds = type_var_kinds.clone();
            for (v, _visible, kind_ann) in vars {
                let var_kind = match kind_ann {
                    Some(k) => convert_kind_expr(k),
                    None => ks.fresh_kind_var(),
                };
                inner_var_kinds.insert(v.value, var_kind);
            }
            infer_kind(ks, ty, &inner_var_kinds, type_ops, self_type)
        }

        TypeExpr::Constrained { constraints, ty, .. } => {
            // Check constraint argument kinds against the class's expected parameter kinds
            for constraint in constraints {
                let class_kind = ks.lookup_type_fresh(constraint.class.name);
                if let Some(class_kind) = class_kind {
                    let class_kind = instantiate_kind(ks, &class_kind);
                    let mut remaining = class_kind;
                    for arg in &constraint.args {
                        let arg_kind = infer_kind(ks, arg, type_var_kinds, type_ops, self_type)?;
                        let result = ks.fresh_kind_var();
                        let expected = Type::fun(arg_kind, result.clone());
                        ks.unify_kinds(constraint.span, &expected, &remaining)?;
                        remaining = result;
                    }
                } else {
                    // Unknown class — just infer arg kinds without checking
                    for arg in &constraint.args {
                        infer_kind(ks, arg, type_var_kinds, type_ops, self_type)?;
                    }
                }
            }
            infer_kind(ks, ty, type_var_kinds, type_ops, self_type)
        }

        TypeExpr::Record { fields, .. } => {
            // Record fields are typically kind Type, but we just infer each field's
            // kind without constraining — the unification will catch mismatches.
            for field in fields {
                let _field_kind = infer_kind(ks, &field.ty, type_var_kinds, type_ops, self_type)?;
            }
            Ok(Type::kind_type())
        }

        TypeExpr::Row { span, fields, tail, is_record } => {
            // Row fields can have any kind k (polykinded rows: Row k).
            // All fields must have the same kind.
            let elem_kind = if fields.is_empty() {
                ks.fresh_kind_var()
            } else {
                let first_kind = infer_kind(ks, &fields[0].ty, type_var_kinds, type_ops, self_type)?;
                for field in &fields[1..] {
                    let field_kind = infer_kind(ks, &field.ty, type_var_kinds, type_ops, self_type)?;
                    ks.unify_kinds(*span, &first_kind, &field_kind)?;
                }
                first_kind
            };
            if let Some(tail_expr) = tail {
                let tail_kind = infer_kind(ks, tail_expr, type_var_kinds, type_ops, self_type)?;
                if !*is_record {
                    // Bare row: tail should have kind Row k
                    let row_k = Type::kind_row_of(elem_kind.clone());
                    ks.unify_kinds(*span, &row_k, &tail_kind)?;
                }
            }
            if *is_record {
                // { fields | tail } is sugar for Record (fields | tail), kind Type
                Ok(Type::kind_type())
            } else {
                // ( fields | tail ) is a bare row, kind Row k
                Ok(Type::kind_row_of(elem_kind))
            }
        }

        TypeExpr::Parens { ty, .. } => infer_kind(ks, ty, type_var_kinds, type_ops, self_type),

        TypeExpr::Kinded { span, ty, kind } => {
            let inferred_kind = infer_kind(ks, ty, type_var_kinds, type_ops, self_type)?;
            let annotated_kind = convert_kind_expr(kind);
            ks.unify_kinds(*span, &annotated_kind, &inferred_kind)?;
            Ok(annotated_kind)
        }

        TypeExpr::TypeOp { span, left, op, right } => {
            let op_name = op.value.name;
            let resolved = type_ops.get(&op_name).copied().unwrap_or(op_name);
            let op_kind = match ks.lookup_type(resolved) {
                Some(k) => k.clone(),
                None => ks.fresh_kind_var(),
            };
            let left_kind = infer_kind(ks, left, type_var_kinds, type_ops, self_type)?;
            let right_kind = infer_kind(ks, right, type_var_kinds, type_ops, self_type)?;

            // op :: k1 -> k2 -> k3
            let result_kind = ks.fresh_kind_var();
            let k2_to_result = Type::fun(right_kind, result_kind.clone());
            let expected_op_kind = Type::fun(left_kind, k2_to_result);
            ks.unify_kinds(*span, &expected_op_kind, &op_kind)?;
            Ok(result_kind)
        }

        TypeExpr::StringLiteral { .. } => Ok(Type::kind_symbol()),
        TypeExpr::IntLiteral { .. } => Ok(Type::kind_int()),

        TypeExpr::Wildcard { .. } => Ok(ks.fresh_kind_var()),
        TypeExpr::Hole { .. } => Ok(ks.fresh_kind_var()),
    }
}

/// Infer the kind of a data type declaration.
/// Returns the inferred kind (e.g., `Type -> Type -> Type` for `data Pair a b = ...`).
pub fn infer_data_kind(
    ks: &mut KindState,
    name: Symbol,
    type_vars: &[crate::cst::Spanned<Symbol>],
    type_var_kind_anns: &[Option<Box<TypeExpr>>],
    constructors: &[crate::cst::DataConstructor],
    span: Span,
    type_ops: &HashMap<Symbol, Symbol>,
) -> Result<Type, TypeError> {
    let k_type = Type::kind_type();
    let mut var_kinds = HashMap::new();

    // Assign kind to each type variable (from annotation or fresh)
    for (i, tv) in type_vars.iter().enumerate() {
        let var_kind = if let Some(Some(kind_ann)) = type_var_kind_anns.get(i) {
            convert_kind_expr(kind_ann)
        } else {
            ks.fresh_kind_var()
        };
        var_kinds.insert(tv.value, var_kind);
    }

    // Check each constructor field has kind Type
    // Pass self_type=Some(name) to avoid freshening self-references (enables infinite kind detection)
    for ctor in constructors {
        for field_te in &ctor.fields {
            let field_kind = infer_kind(ks, field_te, &var_kinds, type_ops, Some(name))?;
            ks.unify_kinds(span, &k_type, &field_kind)?;
        }
    }

    // Build the overall kind: k1 -> k2 -> ... -> Type
    let mut result_kind = k_type;
    for tv in type_vars.iter().rev() {
        let var_kind = ks.zonk_kind(var_kinds[&tv.value].clone());
        result_kind = Type::fun(var_kind, result_kind);
    }

    Ok(result_kind)
}

/// Infer the kind of a newtype declaration.
pub fn infer_newtype_kind(
    ks: &mut KindState,
    name: Symbol,
    type_vars: &[crate::cst::Spanned<Symbol>],
    type_var_kind_anns: &[Option<Box<TypeExpr>>],
    field_ty: &TypeExpr,
    span: Span,
    type_ops: &HashMap<Symbol, Symbol>,
) -> Result<Type, TypeError> {
    let k_type = Type::kind_type();
    let mut var_kinds = HashMap::new();

    for (i, tv) in type_vars.iter().enumerate() {
        let var_kind = if let Some(Some(kind_ann)) = type_var_kind_anns.get(i) {
            convert_kind_expr(kind_ann)
        } else {
            ks.fresh_kind_var()
        };
        var_kinds.insert(tv.value, var_kind);
    }

    // The single field must have kind Type
    let field_kind = infer_kind(ks, field_ty, &var_kinds, type_ops, Some(name))?;
    ks.unify_kinds(span, &k_type, &field_kind)?;

    // Build kind: k1 -> k2 -> ... -> Type
    let mut result_kind = k_type;
    for tv in type_vars.iter().rev() {
        let var_kind = ks.zonk_kind(var_kinds[&tv.value].clone());
        result_kind = Type::fun(var_kind, result_kind);
    }

    Ok(result_kind)
}

/// Infer the kind of a type alias declaration.
pub fn infer_type_alias_kind(
    ks: &mut KindState,
    name: Symbol,
    type_vars: &[crate::cst::Spanned<Symbol>],
    type_var_kind_anns: &[Option<Box<TypeExpr>>],
    body: &TypeExpr,
    _span: Span,
    type_ops: &HashMap<Symbol, Symbol>,
) -> Result<Type, TypeError> {
    let mut var_kinds = HashMap::new();

    for (i, tv) in type_vars.iter().enumerate() {
        let var_kind = if let Some(Some(kind_ann)) = type_var_kind_anns.get(i) {
            convert_kind_expr(kind_ann)
        } else {
            ks.fresh_kind_var()
        };
        var_kinds.insert(tv.value, var_kind);
    }

    let body_kind = infer_kind(ks, body, &var_kinds, type_ops, Some(name))?;

    // Build kind: k1 -> k2 -> ... -> body_kind
    let mut result_kind = body_kind;
    for tv in type_vars.iter().rev() {
        let var_kind = ks.zonk_kind(var_kinds[&tv.value].clone());
        result_kind = Type::fun(var_kind, result_kind);
    }

    Ok(result_kind)
}

/// Infer the kind of a class declaration.
/// Classes have kind `k1 -> k2 -> ... -> Constraint`.
pub fn infer_class_kind(
    ks: &mut KindState,
    name: Symbol,
    type_vars: &[crate::cst::Spanned<Symbol>],
    members: &[crate::cst::ClassMember],
    _span: Span,
    type_ops: &HashMap<Symbol, Symbol>,
) -> Result<Type, TypeError> {
    let mut var_kinds = HashMap::new();

    for tv in type_vars {
        let var_kind = ks.fresh_kind_var();
        var_kinds.insert(tv.value, var_kind);
    }

    // Check member type signatures
    for member in members {
        let _member_kind = infer_kind(ks, &member.ty, &var_kinds, type_ops, Some(name))?;
    }

    // Build kind: k1 -> k2 -> ... -> Constraint
    let mut result_kind = Type::kind_constraint();
    for tv in type_vars.iter().rev() {
        let var_kind = ks.zonk_kind(var_kinds[&tv.value].clone());
        result_kind = Type::fun(var_kind, result_kind);
    }

    Ok(result_kind)
}

/// Create a temporary KindState for usage-site kind checking (type signatures, instance heads).
/// Properly remaps unsolved unification variables from the main state to fresh variables
/// in the temp state, avoiding cross-contamination and index-out-of-bounds panics.
pub fn create_temp_kind_state(ks: &mut KindState) -> KindState {
    use crate::typechecker::types::TyVarId;

    let mut tmp = KindState {
        state: UnifyState::new(),
        type_kinds: HashMap::new(),
        binding_group: HashSet::new(),
    };
    let mut mapping: HashMap<TyVarId, Type> = HashMap::new();

    for (&name, kind) in &ks.type_kinds {
        let zonked = ks.state.zonk(kind.clone());
        let remapped = remap_unif_vars(&zonked, &mut mapping, &mut tmp);
        tmp.type_kinds.insert(name, remapped);
    }
    // Copy type aliases so the temp state can expand them
    tmp.state.type_aliases = ks.state.type_aliases.clone();
    tmp
}

/// Replace unsolved Unif vars in a type with fresh vars from the temp state.
/// Each unique old var ID maps to a single new fresh var (preserving sharing).
fn remap_unif_vars(
    ty: &Type,
    mapping: &mut HashMap<crate::typechecker::types::TyVarId, Type>,
    tmp: &mut KindState,
) -> Type {
    match ty {
        Type::Unif(id) => {
            mapping.entry(*id).or_insert_with(|| tmp.fresh_kind_var()).clone()
        }
        Type::Fun(from, to) => {
            Type::fun(
                remap_unif_vars(from, mapping, tmp),
                remap_unif_vars(to, mapping, tmp),
            )
        }
        Type::App(f, a) => {
            Type::app(
                remap_unif_vars(f, mapping, tmp),
                remap_unif_vars(a, mapping, tmp),
            )
        }
        Type::Forall(vars, body) => {
            Type::Forall(vars.clone(), Box::new(remap_unif_vars(body, mapping, tmp)))
        }
        _ => ty.clone(),
    }
}

/// Check a newtype/data body against a skolemized standalone kind signature.
/// This catches cases where the body over-constrains the kind (e.g., forcing independent
/// kind variables to be the same). Uses rigid skolem symbols instead of unification variables,
/// so that independent forall-bound kind vars cannot accidentally unify.
pub fn check_body_against_standalone_kind(
    ks: &mut KindState,
    standalone: &Type,
    type_vars: &[crate::cst::Spanned<Symbol>],
    body_fields: &[&TypeExpr],
    name: Symbol,
    span: Span,
    type_ops: &HashMap<Symbol, Symbol>,
) -> Option<TypeError> {
    // Only applies to forall-quantified standalone kinds
    if !matches!(standalone, Type::Forall(..)) {
        return None;
    }

    // Skolemize: replace forall-bound vars with rigid Con symbols
    let skolemized = skolemize_kind(standalone);
    let param_kinds = extract_param_kinds(&skolemized, type_vars.len());
    if param_kinds.len() != type_vars.len() {
        return None;
    }

    // Build var_kinds map with skolemized parameter kinds
    let mut var_kinds = HashMap::new();
    for (tv, pk) in type_vars.iter().zip(param_kinds.iter()) {
        var_kinds.insert(tv.value, pk.clone());
    }

    // Create a temp state for this check
    let mut tmp = create_temp_kind_state(ks);

    // Try to kind-check each body field with skolemized var kinds
    let k_type = Type::kind_type();
    for field in body_fields {
        match infer_kind(&mut tmp, field, &var_kinds, type_ops, Some(name)) {
            Ok(field_kind) => {
                if let Err(_) = tmp.unify_kinds(span, &k_type, &field_kind) {
                    return Some(TypeError::KindMismatch {
                        span,
                        expected: k_type,
                        found: tmp.zonk_kind(field_kind),
                    });
                }
            }
            Err(e) => return Some(e),
        }
    }

    None
}

/// Kind-check a standalone type expression (used for type signatures and annotations).
/// Creates a temporary KindState to avoid polluting the main state.
/// Checks that the resulting kind is Type (since value-level types must have kind Type).
pub fn check_type_expr_kind(
    ks: &mut KindState,
    te: &TypeExpr,
    type_ops: &HashMap<Symbol, Symbol>,
) -> Result<Type, TypeError> {
    let mut tmp = create_temp_kind_state(ks);
    let empty_var_kinds = HashMap::new();
    let kind = infer_kind(&mut tmp, te, &empty_var_kinds, type_ops, None)?;
    // Value-level types must have kind Type
    let k_type = Type::kind_type();
    let zonked = tmp.zonk_kind(kind);
    if zonked != k_type && !matches!(zonked, Type::Unif(_)) {
        return Err(TypeError::ExpectedType {
            span: te.span(),
            found: zonked,
        });
    }
    Ok(zonked)
}

/// Kind-check instance head type args against the class's expected parameter kinds.
/// Creates a temporary KindState per call to avoid cross-contamination between instances.
pub fn check_instance_head_kinds(
    ks: &mut KindState,
    class_name: Symbol,
    types: &[TypeExpr],
    span: Span,
    type_ops: &HashMap<Symbol, Symbol>,
) -> Result<(), TypeError> {
    let mut tmp = create_temp_kind_state(ks);

    // Look up the class kind and instantiate it
    let class_kind = match tmp.lookup_type_fresh(class_name) {
        Some(k) => instantiate_kind(&mut tmp, &k),
        None => return Ok(()), // Unknown class — skip kind checking
    };

    let empty_var_kinds = HashMap::new();
    let mut remaining_kind = class_kind.clone();
    for ty_expr in types {
        let arg_kind = infer_kind(&mut tmp, ty_expr, &empty_var_kinds, type_ops, None)?;
        let result_kind = tmp.fresh_kind_var();
        let expected = Type::fun(arg_kind.clone(), result_kind.clone());
        if let Err(e) = tmp.unify_kinds(span, &expected, &remaining_kind) {
            return Err(e);
        }
        remaining_kind = result_kind;
    }

    Ok(())
}

/// Collect all TypeExpr references from a value declaration's expression tree
/// and kind-check each one. This catches kind errors in inline type annotations
/// like `Pair :: Pair Int "foo"` in expressions.
pub fn check_value_decl_kinds(
    ks: &mut KindState,
    binders: &[crate::cst::Binder],
    guarded: &crate::cst::GuardedExpr,
    where_clause: &[crate::cst::LetBinding],
    type_ops: &HashMap<Symbol, Symbol>,
) -> Vec<TypeError> {
    let mut type_exprs = Vec::new();
    for b in binders {
        collect_type_exprs_from_binder(b, &mut type_exprs);
    }
    collect_type_exprs_from_guarded(guarded, &mut type_exprs);
    for lb in where_clause {
        collect_type_exprs_from_let_binding(lb, &mut type_exprs);
    }

    let mut errors = Vec::new();
    for te in type_exprs {
        if let Err(e) = check_type_expr_kind(ks, te, type_ops) {
            errors.push(e);
        }
    }
    errors
}

fn collect_type_exprs_from_expr<'a>(expr: &'a crate::cst::Expr, out: &mut Vec<&'a TypeExpr>) {
    use crate::cst::Expr;
    match expr {
        Expr::TypeAnnotation { ty, expr, .. } => {
            out.push(ty);
            collect_type_exprs_from_expr(expr, out);
        }
        Expr::VisibleTypeApp { func, .. } => {
            // Don't collect the VTA type arg — it can have any kind, not just Type
            collect_type_exprs_from_expr(func, out);
        }
        Expr::App { func, arg, .. } => {
            collect_type_exprs_from_expr(func, out);
            collect_type_exprs_from_expr(arg, out);
        }
        Expr::Lambda { binders, body, .. } => {
            for b in binders {
                collect_type_exprs_from_binder(b, out);
            }
            collect_type_exprs_from_expr(body, out);
        }
        Expr::Op { left, right, .. } => {
            collect_type_exprs_from_expr(left, out);
            collect_type_exprs_from_expr(right, out);
        }
        Expr::If { cond, then_expr, else_expr, .. } => {
            collect_type_exprs_from_expr(cond, out);
            collect_type_exprs_from_expr(then_expr, out);
            collect_type_exprs_from_expr(else_expr, out);
        }
        Expr::Case { exprs, alts, .. } => {
            for e in exprs {
                collect_type_exprs_from_expr(e, out);
            }
            for alt in alts {
                for b in &alt.binders {
                    collect_type_exprs_from_binder(b, out);
                }
                collect_type_exprs_from_guarded(&alt.result, out);
            }
        }
        Expr::Let { bindings, body, .. } => {
            for lb in bindings {
                collect_type_exprs_from_let_binding(lb, out);
            }
            collect_type_exprs_from_expr(body, out);
        }
        Expr::Do { statements, .. } | Expr::Ado { statements, .. } => {
            for s in statements {
                collect_type_exprs_from_do_statement(s, out);
            }
            if let Expr::Ado { result, .. } = expr {
                collect_type_exprs_from_expr(result, out);
            }
        }
        Expr::Record { fields, .. } => {
            for f in fields {
                if let Some(v) = &f.value {
                    collect_type_exprs_from_expr(v, out);
                }
            }
        }
        Expr::RecordAccess { expr, .. } => {
            collect_type_exprs_from_expr(expr, out);
        }
        Expr::RecordUpdate { expr, updates, .. } => {
            collect_type_exprs_from_expr(expr, out);
            for u in updates {
                collect_type_exprs_from_expr(&u.value, out);
            }
        }
        Expr::Parens { expr, .. } => {
            collect_type_exprs_from_expr(expr, out);
        }
        Expr::Negate { expr, .. } => {
            collect_type_exprs_from_expr(expr, out);
        }
        Expr::Array { elements, .. } => {
            for e in elements {
                collect_type_exprs_from_expr(e, out);
            }
        }
        Expr::AsPattern { name, pattern, .. } => {
            collect_type_exprs_from_expr(name, out);
            collect_type_exprs_from_expr(pattern, out);
        }
        // Terminal nodes with no sub-expressions or type annotations
        Expr::Var { .. } | Expr::Constructor { .. } | Expr::Literal { .. }
        | Expr::OpParens { .. } | Expr::Hole { .. } => {}
    }
}

fn collect_type_exprs_from_binder<'a>(binder: &'a crate::cst::Binder, out: &mut Vec<&'a TypeExpr>) {
    use crate::cst::Binder;
    match binder {
        Binder::Typed { ty, binder, .. } => {
            out.push(ty);
            collect_type_exprs_from_binder(binder, out);
        }
        Binder::Constructor { args, .. } => {
            for a in args {
                collect_type_exprs_from_binder(a, out);
            }
        }
        Binder::Record { fields, .. } => {
            for f in fields {
                if let Some(b) = &f.binder {
                    collect_type_exprs_from_binder(b, out);
                }
            }
        }
        Binder::As { binder, .. } | Binder::Parens { binder, .. } => {
            collect_type_exprs_from_binder(binder, out);
        }
        Binder::Array { elements, .. } => {
            for e in elements {
                collect_type_exprs_from_binder(e, out);
            }
        }
        Binder::Op { left, right, .. } => {
            collect_type_exprs_from_binder(left, out);
            collect_type_exprs_from_binder(right, out);
        }
        Binder::Wildcard { .. } | Binder::Var { .. } | Binder::Literal { .. } => {}
    }
}

fn collect_type_exprs_from_guarded<'a>(g: &'a crate::cst::GuardedExpr, out: &mut Vec<&'a TypeExpr>) {
    use crate::cst::GuardedExpr;
    match g {
        GuardedExpr::Unconditional(expr) => {
            collect_type_exprs_from_expr(expr, out);
        }
        GuardedExpr::Guarded(guards) => {
            for guard in guards {
                for p in &guard.patterns {
                    match p {
                        crate::cst::GuardPattern::Boolean(e) => collect_type_exprs_from_expr(e, out),
                        crate::cst::GuardPattern::Pattern(b, e) => {
                            collect_type_exprs_from_binder(b, out);
                            collect_type_exprs_from_expr(e, out);
                        }
                    }
                }
                collect_type_exprs_from_expr(&guard.expr, out);
            }
        }
    }
}

fn collect_type_exprs_from_let_binding<'a>(lb: &'a crate::cst::LetBinding, out: &mut Vec<&'a TypeExpr>) {
    use crate::cst::LetBinding;
    match lb {
        LetBinding::Value { binder, expr, .. } => {
            collect_type_exprs_from_binder(binder, out);
            collect_type_exprs_from_expr(expr, out);
        }
        LetBinding::Signature { ty, .. } => {
            out.push(ty);
        }
    }
}

fn collect_type_exprs_from_do_statement<'a>(s: &'a crate::cst::DoStatement, out: &mut Vec<&'a TypeExpr>) {
    use crate::cst::DoStatement;
    match s {
        DoStatement::Bind { binder, expr, .. } => {
            collect_type_exprs_from_binder(binder, out);
            collect_type_exprs_from_expr(expr, out);
        }
        DoStatement::Let { bindings, .. } => {
            for lb in bindings {
                collect_type_exprs_from_let_binding(lb, out);
            }
        }
        DoStatement::Discard { expr, .. } => {
            collect_type_exprs_from_expr(expr, out);
        }
    }
}

/// Extract parameter kinds from a function kind.
/// E.g., `k1 -> k2 -> Type` returns `[k1, k2]` and result `Type`.
pub fn extract_param_kinds(kind: &Type, count: usize) -> Vec<Type> {
    let mut result = Vec::new();
    let mut current = kind.clone();
    for _ in 0..count {
        if let Type::Fun(param, rest) = current {
            result.push(*param);
            current = *rest;
        } else {
            break;
        }
    }
    result
}

/// Skolemize a standalone kind signature for checking.
/// Replaces forall-bound variables with rigid Con("$kind_skolem_N") types
/// that cannot unify with each other. Returns the skolemized kind.
pub fn skolemize_kind(kind: &Type) -> Type {
    static COUNTER: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    match kind {
        Type::Forall(vars, body) => {
            let mut subst = HashMap::new();
            for (var, _visible) in vars {
                let n = COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                let skolem = Type::Con(interner::intern(&format!("$kind_skolem_{}", n)));
                subst.insert(*var, skolem);
            }
            substitute_kind_vars(&subst, body)
        }
        other => other.clone(),
    }
}

/// Instantiate a polymorphic kind signature by replacing forall-bound variables
/// with fresh kind unification variables. Returns the instantiated kind.
pub fn instantiate_kind(ks: &mut KindState, kind: &Type) -> Type {
    match kind {
        Type::Forall(vars, body) => {
            let mut subst = HashMap::new();
            for (var, _visible) in vars {
                subst.insert(*var, ks.fresh_kind_var());
            }
            substitute_kind_vars(&subst, body)
        }
        other => other.clone(),
    }
}

/// Collect type constructor names referenced in a TypeExpr.
fn collect_type_refs(te: &TypeExpr, out: &mut HashSet<Symbol>) {
    match te {
        TypeExpr::Constructor { name, .. } => { out.insert(name.name); }
        TypeExpr::App { constructor, arg, .. } => {
            collect_type_refs(constructor, out);
            collect_type_refs(arg, out);
        }
        TypeExpr::Function { from, to, .. } => {
            collect_type_refs(from, out);
            collect_type_refs(to, out);
        }
        TypeExpr::Forall { ty, .. } => collect_type_refs(ty, out),
        TypeExpr::Constrained { ty, constraints, .. } => {
            for c in constraints { for a in &c.args { collect_type_refs(a, out); } }
            collect_type_refs(ty, out);
        }
        TypeExpr::Parens { ty, .. } => collect_type_refs(ty, out),
        TypeExpr::Kinded { ty, kind, .. } => {
            collect_type_refs(ty, out);
            collect_type_refs(kind, out);
        }
        TypeExpr::Record { fields, .. } | TypeExpr::Row { fields, .. } => {
            for f in fields { collect_type_refs(&f.ty, out); }
        }
        TypeExpr::TypeOp { left, right, .. } => {
            collect_type_refs(left, out);
            collect_type_refs(right, out);
        }
        _ => {}
    }
}

/// Compute SCCs of type declarations for kind inference binding groups.
/// Returns groups in topological order (dependencies first).
pub fn compute_type_sccs(decls: &[crate::cst::Decl]) -> Vec<Vec<Symbol>> {
    use crate::cst::Decl;

    // Collect all local type names and their dependencies
    let mut local_types: HashSet<Symbol> = HashSet::new();
    let mut deps: HashMap<Symbol, HashSet<Symbol>> = HashMap::new();

    for decl in decls {
        match decl {
            Decl::Data { name, constructors, kind_sig, is_role_decl, .. } if *kind_sig == crate::cst::KindSigSource::None && !*is_role_decl => {
                local_types.insert(name.value);
                let mut refs = HashSet::new();
                for ctor in constructors {
                    for field in &ctor.fields {
                        collect_type_refs(field, &mut refs);
                    }
                }
                deps.insert(name.value, refs);
            }
            Decl::Newtype { name, ty, .. } => {
                local_types.insert(name.value);
                let mut refs = HashSet::new();
                collect_type_refs(ty, &mut refs);
                deps.insert(name.value, refs);
            }
            Decl::TypeAlias { name, ty, .. } => {
                local_types.insert(name.value);
                let mut refs = HashSet::new();
                collect_type_refs(ty, &mut refs);
                deps.insert(name.value, refs);
            }
            Decl::Class { name, members, is_kind_sig, .. } if !*is_kind_sig => {
                local_types.insert(name.value);
                let mut refs = HashSet::new();
                for m in members {
                    collect_type_refs(&m.ty, &mut refs);
                }
                deps.insert(name.value, refs);
            }
            _ => {}
        }
    }

    // Filter deps to only include local types
    for refs in deps.values_mut() {
        refs.retain(|r| local_types.contains(r));
    }

    // Simple Kosaraju's algorithm for SCC
    let names: Vec<Symbol> = local_types.iter().copied().collect();
    let name_to_idx: HashMap<Symbol, usize> = names.iter().enumerate().map(|(i, &n)| (n, i)).collect();
    let n = names.len();

    // Build adjacency list
    let mut adj: Vec<Vec<usize>> = vec![vec![]; n];
    let mut radj: Vec<Vec<usize>> = vec![vec![]; n];
    for (i, name) in names.iter().enumerate() {
        if let Some(refs) = deps.get(name) {
            for r in refs {
                if let Some(&j) = name_to_idx.get(r) {
                    if i != j {
                        adj[i].push(j);
                        radj[j].push(i);
                    }
                }
            }
        }
    }

    // First pass: compute finish order
    let mut visited = vec![false; n];
    let mut order = Vec::new();
    fn dfs1(u: usize, adj: &[Vec<usize>], visited: &mut [bool], order: &mut Vec<usize>) {
        visited[u] = true;
        for &v in &adj[u] {
            if !visited[v] { dfs1(v, adj, visited, order); }
        }
        order.push(u);
    }
    for i in 0..n {
        if !visited[i] { dfs1(i, &adj, &mut visited, &mut order); }
    }

    // Second pass: assign SCCs in reverse finish order
    let mut comp = vec![usize::MAX; n];
    let mut num_comp = 0;
    fn dfs2(u: usize, c: usize, radj: &[Vec<usize>], comp: &mut [usize]) {
        comp[u] = c;
        for &v in &radj[u] {
            if comp[v] == usize::MAX { dfs2(v, c, radj, comp); }
        }
    }
    for &i in order.iter().rev() {
        if comp[i] == usize::MAX {
            dfs2(i, num_comp, &radj, &mut comp);
            num_comp += 1;
        }
    }

    // Group by component and return in topological order
    let mut groups: Vec<Vec<Symbol>> = vec![vec![]; num_comp];
    for (i, &c) in comp.iter().enumerate() {
        groups[c].push(names[i]);
    }
    groups
}

/// Substitute kind variables in a type (used for instantiating polymorphic kinds).
fn substitute_kind_vars(subst: &HashMap<Symbol, Type>, ty: &Type) -> Type {
    match ty {
        Type::Var(name) => {
            subst.get(name).cloned().unwrap_or_else(|| ty.clone())
        }
        Type::Fun(from, to) => {
            Type::fun(
                substitute_kind_vars(subst, from),
                substitute_kind_vars(subst, to),
            )
        }
        Type::App(f, a) => {
            Type::app(
                substitute_kind_vars(subst, f),
                substitute_kind_vars(subst, a),
            )
        }
        Type::Forall(vars, body) => {
            // Don't substitute vars that are shadowed by this forall
            let mut inner_subst = subst.clone();
            for (v, _) in vars {
                inner_subst.remove(v);
            }
            Type::Forall(vars.clone(), Box::new(substitute_kind_vars(&inner_subst, body)))
        }
        _ => ty.clone(),
    }
}
